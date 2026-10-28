(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_Xpres AsStack0.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxImage FxHandoff FxCellFrame FxRoFrame FxGeom FxGeomA I2Canon I2Mach I2Image I2Run I2RunA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
Record gblk : Type := GB { g_tag : int; g_id : bptr; g_addr : Z; g_size : int }.
(* [comment removed for export] *)
Record gframe : Type := GFr { f_tag : int; f_k : int; f_ff : Z; f_fp : Z }.
Definition ff_of (f : gframe) : fframe := (to_Z (f_k f), f_ff f, f_fp f).

(* [comment removed for export] *)
Record i2aenv : Type := I2AE {
  q_sp0 : Z;                  (* [comment removed for export] *)
  q_lo : Z;                   (* [comment removed for export] *)
  q_B : Z;                    (* [comment removed for export] *)
  q_shi : Z;                  (* [comment removed for export] *)
  q_mo0 : Model;              (* [comment removed for export] *)
  q_F : bvmap 5 word; q_fc : bv 32;   (* [comment removed for export] *)
  q_m0 : word -> option byte; (* [comment removed for export] *)
  q_LB0 : list block;         (* [comment removed for export] *)
  q_LF0 : list fframe;        (* [comment removed for export] *)
  q_n0 : int;                 (* [comment removed for export] *)
  q_rho0 : int -> word;
  q_G0 : list gblk;           (* [comment removed for export] *)
  q_s0 : Z;                   (* [comment removed for export] *)
  q_CH0 : list (Z * Z);       (* [comment removed for export] *)
  q_AL0 : Z;                  (* [comment removed for export] *)
  q_cs : list (int * int * int) }.   (* [comment removed for export] *)

(* [comment removed for export] *)
Section Cost.
  Variable H : asr.
  Definition cost1 (e : int * int * int) : Z :=
    match e with (k, a, b) =>
      if (k =? 0)%uint63 then as_Cm H (to_Z a)
      else if (k =? 1)%uint63 then as_Cf H (to_Z a)
      else if (k =? 2)%uint63 then as_Cm H (to_Z b) + as_Cf H (to_Z a)
      else as_Cm H (to_Z a + to_Z b)          (* [comment removed for export] *)
    end.
  Definition csum (l : list (int * int * int)) : Z := fold_right (fun e acc => cost1 e + acc) 0 l.
  Lemma csum_app : forall l1 l2, csum (l1 ++ l2) = csum l1 + csum l2.
  Proof. induction l1 as [|e l1 IH]; intros l2; cbn [csum fold_right app]; [reflexivity|]. unfold csum in IH. rewrite IH. apply Z.add_assoc. Qed.
End Cost.

Section Inv.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable IMX : fimage.            (* [comment removed for export] *)
  Variable A : i2aconsts.
  Let K := ka_K A.
  Let IM := im_ro IMX.
  Let RO := ro_of K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition rb_addr (a : Z) : Prop := exists b, In b (c_rb K) /\ to_Z b = a.
  Definition xw_addr (a : Z) : Prop := (exists c, In c (c_xw K) /\ to_Z c <= a < to_Z c + 8) /\ ~ rb_addr a.
  Definition err_addr (a : Z) : Prop := to_Z (c_errcell K) <= a < to_Z (c_errcell K) + 8 /\ ~ rb_addr a.
  Definition errA : Z := to_Z (c_errcell K) + to_Z (c_errbi K).
  (* [comment removed for export] *)
  Definition named_addr (Q : i2aenv) (a : Z) : Prop :=
    exists g, In g (q_G0 Q) /\ (g_addr g <= a < g_addr g + to_Z (g_size g) \/ sh (g_addr g) <= a < sh (g_addr g) + nsh (to_Z (g_size g))).
  Definition client0 (Q : i2aenv) (a : Z) : Prop := aclient_addr H (q_LB0 Q) (q_sp0 Q) a.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition awin_b (lo hi : Z) : bool :=
    ((0x5ea840 <=? lo) && (hi <=? 0x5ea848)) || ((0x5ed1a0 <=? lo) && (hi <=? 0x5edfa0)) || ((0x6a7248 <=? lo) && (hi <=? 0x6a7298))
    || ((0xbccf50 <=? lo) && (hi <=? ATLS_PRIV_LO)) || ((ATLS_PRIV_HI <=? lo) && (hi <=? ALIBC_PGSZ)) || ((ALIBC_PGSZ + 8 <=? lo) && (hi <=? ATSD0))
    || ((ATSD0 + 8 <=? lo) && (hi <=? 0xc03570)).
  (* [comment removed for export] *)
  Definition aconst_okb (lo hi : Z) : bool :=
    ((hi <=? 0x571000) || (0x5eaa78 <=? lo))
    && ((hi <=? ASHBASE_CELL) || (ASHBASE_CELL + 12 <=? lo)) && ((hi <=? AMEMCPYP_CELL) || (AMEMCPYP_CELL + 16 <=? lo))
    && ((hi <=? AINITED_CELL) || (AINITED_CELL + 2 <=? lo)) && ((hi <=? AHIEND_CELL) || (AHIEND_CELL + 24 <=? lo))
    && ((hi <=? ADYING_CELL) || (ADYING_CELL + 4 <=? lo)) && ((hi <=? APGSZ_CELL) || (APGSZ_CELL + 8 <=? lo))
    && ((hi <=? ACANPOISON_CELL) || (ACANPOISON_CELL + 1 <=? lo)) && ((hi <=? 0x73c428) || (0x73c554 <=? lo))
    && ((hi <=? 0x6a80f8) || (0x6a81b8 <=? lo)) && ((hi <=? AVERBOSITY_CELL) || (AVERBOSITY_CELL + 4 <=? lo))
    && ((hi <=? AREAL_TLSGA_CELL) || (AREAL_TLSGA_CELL + 8 <=? lo)) && ((hi <=? ATSD_CELL) || (ATSD_CELL + 8 <=? lo))
    && ((hi <=? 0xbe1c38) || (0xbe1cd0 <=? lo))
    && ((hi <=? AREGISTERED_CELL) || (AREGISTERED_CELL + 8 <=? lo)) && ((hi <=? ACOVFLAG_CELL) || (ACOVFLAG_CELL + 1 <=? lo))
    && ((hi <=? sh AIMG_LO) || (sh AIMG_TOP <=? lo)).
  Definition xw_cell_ok (c : int) : bool :=
    ((c land 7 =? 0)%uint63)
    && awin_b (to_Z c) (to_Z c + 8) && aconst_okb (to_Z c) (to_Z c + 8)
    && ((to_Z c + 8 <=? AERRNO)%Z || (AERRNO + 4 <=? to_Z c)%Z).
  Definition K_err_ok : bool :=
    (to_Z (c_errcell K) + to_Z (c_errbi K) =? AERRNO)%Z && ((c_errcell K land 7 =? 0)%uint63) && (to_Z (c_errbi K) + 4 <=? 8)%Z
    && awin_b (to_Z (c_errcell K)) (to_Z (c_errcell K) + 8) && aconst_okb (to_Z (c_errcell K)) (to_Z (c_errcell K) + 8)
    && (to_Z (c_tp K) =? ATP)%Z
    && (AMALLOC_STACK <=? to_Z (c_mstack K))%Z && (AREALLOC_STACK <=? to_Z (c_mstack K))%Z && (AFREE_STACK <=? to_Z (c_mstack K))%Z
    && (to_Z (c_mstack K) <=? to_Z (c_stack K))%Z
    && (to_Z (ka_fstack A) =? AFS_STACK)%Z && (to_Z (ka_istack A) =? AINTRIN_STACK)%Z
    && (AFS_STACK <=? to_Z (c_stack K))%Z && (AINTRIN_STACK <=? to_Z (c_stack K))%Z
    && ((c_stack K land 15 =? 0)%uint63) && (to_Z (c_stack K) <=? 2 ^ 40)%Z.
  Definition K_pcs_ok : bool :=
    forallb (fun p => (to_Z p =? AMALLOC_STUB)%Z) (ka_malloc A)
    && forallb (fun p => (to_Z p =? AFREE_STUB)%Z) (ka_free A)
    && forallb (fun p => (to_Z p =? AREALLOC_STUB)%Z) (ka_realloc A)
    && (to_Z (ka_memset A) =? AASAN_MEMSET)%Z
    && forallb (fun p => (to_Z p =? AASAN_MEMCPY)%Z || (to_Z p =? AMEMCPY_STUB)%Z) (ka_memcpy A)
    && (to_Z (ka_memmove A) =? AASAN_MEMMOVE)%Z
    && (to_Z (ka_strlen A) =? ASTRLEN_STUB)%Z
    && forallb (fun pk : int * int => ((to_Z (fst pk) =? AFS_MALLOC_0)%Z && (snd pk =? 0)%uint63)
                                   || ((to_Z (fst pk) =? AFS_MALLOC_1)%Z && (snd pk =? 1)%uint63)
                                   || ((to_Z (fst pk) =? AFS_MALLOC_2)%Z && (snd pk =? 2)%uint63)
                                   || ((to_Z (fst pk) =? AFS_MALLOC_4)%Z && (snd pk =? 4)%uint63)) (ka_fsm A)
    && (to_Z (ka_pc0m A) =? APC0_MALLOC)%Z && (to_Z (ka_pc0f A) =? APC0_FREE)%Z && (to_Z (ka_pc0r A) =? APC0_REALLOC)%Z.
  Definition K_ro_ok : bool :=
    forallb (fun ac : int * cell => ((fst ac land 7 =? 0)%uint63) && (AIMG_LO <=? to_Z (fst ac))%Z && (to_Z (fst ac) + 8 <=? AIMG_TOP)%Z
                                    && negb (existsb (fun c => (c =? fst ac)%uint63) (c_xw K))
                                    && negb ((fst ac =? c_errcell K)%uint63)) (c_ro K).
  Definition K_caps_ok : bool :=
    (to_Z (c_cost K) <? 2 ^ 60)%Z && (to_Z (c_cnt K) <? 2 ^ 60)%Z && (to_Z (ka_fsmax A) <? 2 ^ 60)%Z.
  Definition K_rb_ok : bool :=
    forallb (fun b : int => (AIMG_LO <=? to_Z b)%Z && (to_Z b <? AIMG_TOP)%Z) (c_rb K).
  (* [comment removed for export] *)
  Definition K_sh0_ok : bool :=
    (to_Z (ka_sh0lo A) =? sh AIMG_LO)%Z && (to_Z (ka_sh0len A) =? sh AIMG_TOP)%Z
    && forallb (fun ac : int * cell => ((fst ac land 7 =? 0)%uint63) && (sh AIMG_LO <=? to_Z (fst ac))%Z && (to_Z (fst ac) + 8 <=? sh AIMG_TOP)%Z
                                       && match snd ac with
                                          | CV (FV t _) => (t =? 0)%uint63
                                          | CB sl => forallb (fun j : int => match sget j sl with SK b => (b <? 256)%uint63 | SU => true | SV _ _ => false end)
                                                             [0; 1; 2; 3; 4; 5; 6; 7]%uint63
                                          | CU => false end) (ka_sh0 A).
  Definition KA_ok : bool :=
    forallb xw_cell_ok (c_xw K) && K_err_ok && K_pcs_ok && K_ro_ok && K_caps_ok && K_rb_ok && K_sh0_ok.

  (* [comment removed for export] *)
  Definition sh0_cell (m : mem) (a : Z) (c : cell) : Prop :=
    match c with
    | CV (FV _ w) => bytes_at asegs m a (Z_to_le_bytes 8 (wZ w))
    | CB sl => forall j : int, 0 <= to_Z j < 8 ->
               match sget j sl with
               | SK b => mrd asegs m (wa (a + to_Z j)) = Some (Z_to_bv 8 (to_Z b))
               | SU => True
               | SV _ _ => False
               end
    | CU => False
    end.
  Definition sh0_facts (m : mem) : Prop :=
    Forall (fun ac : int * cell => sh0_cell m (to_Z (fst ac)) (snd ac)) (ka_sh0 A).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition LF_of (Q : i2aenv) (FF : list gframe) : list fframe := map ff_of FF ++ q_LF0 Q.

  Record I2RAX (Q : i2aenv) (st : i2ast) (rho : int -> word) (msF : machine_state) (mo : Model)
         (s : as_St H) (LB : list block) (G : list gblk) (FF : list gframe) (XS : list (Z * Z)) (ms : machine_state) : Prop := mkI2RAX {
    r_vis : as_VIS H s msF = ms ;
    r_Rn : Rn asegs IM (a_n st) rho (a_F st) ms ;
    r_canon : canonR (ms_regs ms) ;
    r_fregs : ms_fregs ms = q_F Q ;
    r_fcsr : ms_fcsr ms = q_fc Q ;
    r_rom : ms_rom ms = seg_rom asegs ;
    r_rho0 : rho 0%uint63 = Z_to_bv 64 0 ;
    r_rho1 : rho 1%uint63 = wa (q_sp0 Q - to_Z (c_stack K)) ;
    r_rho2 : rho 2%uint63 = wa (sh (q_sp0 Q - to_Z (c_stack K))) ;
    r_rho3 : rho 3%uint63 = Z_to_bv 64 0 ;
    r_agree : agree (q_n0 Q) (q_rho0 Q) rho ;
    r_n0 : 4 <= to_Z (q_n0 Q) <= to_Z (a_n st) /\ to_Z (a_n st) < 2 ^ 60 ;
    r_akrel : as_AKREL H s (mkCfg msF mo) ;
    r_mpres : as_MPRES H (q_mo0 Q) mo ;
    r_heap : as_RHEAP H s LB (ms_mem ms) ;
    r_rfs : as_RFS H (LF_of Q FF) (ms_mem ms) ;
    r_aconst : ACONST (ms_mem ms) ;
    r_stack0 : stack0 (ms_mem ms) (q_lo Q) (q_shi Q) ;
    r_chain : as_chain H (ms_mem ms) (q_s0 Q) (q_CH0 Q) ;
    r_CH0 : forall fp ra, In (fp, ra) (q_CH0 Q) -> q_sp0 Q + 16 <= fp ;
    r_s0v : bv_unsigned (q_rho0 Q (ka_ts0 A)) = q_s0 Q /\ to_Z (ka_ts0 A) < to_Z (q_n0 Q) /\ to_Z (c_tra K) < to_Z (q_n0 Q) ;
    r_pfo : pf_ok (as_TR H) (map (fun e : int * list int => (to_Z (fst e), map to_Z (snd e))) (ka_pfo A))
                  (bv_unsigned (q_rho0 Q (c_tra K))) (q_CH0 Q) ;
    r_AL : exists done, q_cs Q = done ++ a_cs st /\ as_AL H s >= q_AL0 Q - csum H done ;
    r_AL0 : csum H (q_cs Q) <= q_AL0 Q ;
    (* [comment removed for export] *)
    r_G : a_blk st = map (fun g => (g_tag g, g_size g)) G ;
    r_Gin : Forall (fun g => In (g_id g, g_addr g, to_Z (g_size g)) LB
                            /\ rho (g_tag g) = wa (g_addr g)
                            /\ 1 <= to_Z (g_size g)
                            /\ 4 <= to_Z (g_tag g) /\ to_Z (g_tag g) + 1 < to_Z (a_n st)
                            /\ (exists rg, iget (g_tag g) (f_mem (a_F st)) = Some rg
                                 /\ rg_lo rg = 0%uint63 /\ rg_len rg = g_size g /\ rg_kind rg = RK_plain /\ (3 <= to_Z (rg_align rg))%Z
                                 /\ rg_dflt rg = Some PKUnk)   (* [comment removed for export] *)
                            /\ (forall rg', iget (g_tag g + 1)%uint63 (f_mem (a_F st)) = Some rg' ->
                                   rg' = sh_region false (g_tag g) (g_size g)
                                   /\ rho (g_tag g + 1)%uint63 = wa (sh (g_addr g))
                                   /\ addressable (ms_mem ms) (g_addr g) (to_Z (g_size g)))) G ;
    r_Gnodup : List.NoDup (map g_id G) ;
    r_Gtnd : List.NoDup (map g_tag G) ;
    r_Gnew : Forall (fun g => In g (q_G0 Q)
                             \/ ((forall a, client0 Q a -> ~ named_addr Q a ->
                                    ~ (g_addr g <= a < g_addr g + to_Z (g_size g))
                                    /\ ~ (sh (g_addr g) <= a < sh (g_addr g) + nsh (to_Z (g_size g))))
                                 /\ (forall b, In b (q_LB0 Q) -> ~ In (blk_id b) (map g_id (q_G0 Q)) -> g_id g <> blk_id b)
                                 /\ to_Z (q_n0 Q) <= to_Z (g_tag g))) G ;   (* [comment removed for export] *)
    r_Gstk : Forall (fun g => stk asegs (ms_mem ms) (g_addr g) (g_addr g + to_Z (g_size g))) G ;
    (* [comment removed for export] *)
    r_FF : a_ff st = map (fun f => (f_tag f, f_k f)) FF ;
    r_FFin : Forall (fun f =>
                 rho (f_tag f) = wa (f_ff f) /\ rho (f_tag f + 1)%uint63 = wa (sh (f_ff f)) /\ rho (f_tag f + 2)%uint63 = wa (f_fp f)
                 /\ 0 <= to_Z (f_k f) <= 6
                 /\ 4 <= to_Z (f_tag f) /\ to_Z (f_tag f) + 2 < to_Z (a_n st)
                 /\ (exists rg, iget (f_tag f) (f_mem (a_F st)) = Some rg
                      /\ rg_lo rg = 0%uint63 /\ rg_len rg = I2RunA.fsz (f_k f) /\ rg_kind rg = RK_plain /\ (6 <= to_Z (rg_align rg))%Z
                      /\ rg_dflt rg = Some PKUnk)
                 /\ (exists rg', iget (f_tag f + 1)%uint63 (f_mem (a_F st)) = Some rg'
                      /\ rg_lo rg' = 0%uint63 /\ to_Z (rg_len rg') = fshn (to_Z (f_k f)) /\ rg_kind rg' = RK_shadow (f_tag f))
                 /\ iget (f_tag f + 2)%uint63 (f_mem (a_F st)) = Some flag_region
                 /\ rin_ivs XS (f_ff f) /\ (forall a, f_ff f <= a < f_ff f + AsIface.fsz (to_Z (f_k f)) -> rin_ivs XS a)
                 /\ (forall a, sh (f_ff f) <= a < sh (f_ff f) + fshn (to_Z (f_k f)) -> rin_ivs XS a)
                 /\ rin_ivs XS (f_fp f)) FF ;
    r_FFnd : List.NoDup (map f_ff FF ++ map ff_addr (q_LF0 Q)) ;
    r_FFtnd : List.NoDup (map f_tag FF) ;
    (* [comment removed for export] *)
    r_tagsep : (forall g g', In g G -> In g' G -> g <> g' -> to_Z (g_tag g) + 2 <= to_Z (g_tag g') \/ to_Z (g_tag g') + 2 <= to_Z (g_tag g))
               /\ (forall g f, In g G -> In f FF -> to_Z (g_tag g) + 2 <= to_Z (f_tag f) \/ to_Z (f_tag f) + 3 <= to_Z (g_tag g))
               /\ (forall f f', In f FF -> In f' FF -> f <> f' -> to_Z (f_tag f) + 3 <= to_Z (f_tag f') \/ to_Z (f_tag f') + 3 <= to_Z (f_tag f)) ;
    r_FFlen : (length FF + length (q_LF0 Q) + (Z.to_nat (to_Z (ka_fsmax A)) - length FF) <= AFS_MAXLIVE)%nat ;
    r_XS : Forall (fs_scratch H (q_LF0 Q)) XS ;
    (* [comment removed for export] *)
    r_dom : forall t rg, iget t (f_mem (a_F st)) = Some rg ->
              t = 0%uint63 \/ t = 1%uint63 \/ t = 2%uint63 \/ t = 3%uint63
              \/ In t (map g_tag G) \/ In t (map (fun g => (g_tag g + 1)%uint63) G)
              \/ In t (map f_tag FF) \/ In t (map (fun f => (f_tag f + 1)%uint63) FF) \/ In t (map (fun f => (f_tag f + 2)%uint63) FF) ;
    r_r0 : exists rg0, iget 0%uint63 (f_mem (a_F st)) = Some rg0
             /\ to_Z (rg_lo rg0) = AIMG_LO /\ to_Z (rg_len rg0) = AIMG_TOP /\ rg_dflt rg0 = None
             /\ forall pn p, iget pn (rg_pages rg0) = Some p -> seg_wr_page IMX pn = true /\ pg_kind p = PKUnk ;
    r_r1 : exists rg1, iget 1%uint63 (f_mem (a_F st)) = Some rg1
             /\ rg_lo rg1 = 0%uint63 /\ rg_len rg1 = c_stack K /\ rg_dflt rg1 = Some PKUnk /\ rg_kind rg1 = RK_plain /\ to_Z (rg_align rg1) = 5 ;
    r_r2 : iget 2%uint63 (f_mem (a_F st)) = Some (sh_region false 1%uint63 (c_stack K)) ;
    r_r3 : iget 3%uint63 (f_mem (a_F st)) = Some (abs_region (ka_sh0lo A) (ka_sh0len A) (ka_sh0 A)) ;
    r_ro : ro_in_r0 RO (f_mem (a_F st)) ;
    r_inb : cells_inb (f_mem (a_F st)) ;
    r_kinds : kinds_ok (f_mem (a_F st)) ;
    (* [comment removed for export] *)
    r_cost : lb_bytes LB + (to_Z (c_cost K) - to_Z (a_cost st)) <= as_LIVE_MAX H /\ to_Z (a_cost st) <= to_Z (c_cost K)
             /\ lb_bytes LB <= lb_bytes (q_LB0 Q) + to_Z (a_cost st) ;
    r_cnt : Z.of_nat (length LB) + (to_Z (c_cnt K) - to_Z (a_cnt st)) <= as_LIVE_CNT_MAX H /\ to_Z (a_cnt st) <= to_Z (c_cnt K)
             /\ Z.of_nat (length LB) <= Z.of_nat (length (q_LB0 Q)) + to_Z (a_cnt st) ;
    (* [comment removed for export] *)
    r_stk : stk asegs (ms_mem ms) (q_lo Q) (q_sp0 Q) ;
    r_lo : aceil <= q_lo Q /\ q_lo Q <= q_sp0 Q - to_Z (c_stack K) /\ q_sp0 Q <= q_B Q /\ q_sp0 Q mod 16 = 0
           /\ (q_sp0 Q - to_Z (c_stack K)) mod 32 = 0 /\ q_sp0 Q < 2 ^ 64 /\ q_sp0 Q <= q_shi Q ;   (* [comment removed for export] *)
    r_auxv : as_rauxv_ok H (ms_mem ms) (q_B Q) ;
    r_inv : mem_inv asegs (ms_mem ms) ;
    r_err : stk asegs (ms_mem ms) errA (errA + 4) ;
    r_sh0 : sh0_facts (ms_mem ms) ;
    (* [comment removed for export] *)
    r_LB0 : forall b, In b (q_LB0 Q) -> ~ In (blk_id b) (map g_id (q_G0 Q)) -> In b LB ;
    r_LB0h : forall b, In b (q_LB0 Q) -> 0 <= blk_addr b /\ blk_addr b + blk_size b <= aceil ;
    r_named0 : Forall (fun g => In (g_id g, g_addr g, to_Z (g_size g)) (q_LB0 Q)) (q_G0 Q) /\ List.NoDup (map blk_id (q_LB0 Q)) ;
    r_LBsub : forall b, In b LB -> In b (q_LB0 Q) \/ exists g, In g G /\ b = (g_id g, g_addr g, to_Z (g_size g)) ;
    (* [comment removed for export] *)
    r_frame : forall a, 0 <= a < 2 ^ 64 -> client0 Q a -> ~ named_addr Q a -> ~ xw_addr a -> ~ err_addr a -> ~ rin_ivs XS a ->
              ms_mem ms (wa a) = q_m0 Q (wa a) ;
    (* [comment removed for export] *)
    r_FFstk : Forall (fun f => stk asegs (ms_mem ms) (f_ff f) (f_ff f + AsIface.fsz (to_Z (f_k f)))) FF
  }.

  Definition I2RA (Q : i2aenv) (st : i2ast) (rho : int -> word) (msF : machine_state) (mo : Model) : Prop :=
    exists s LB G FF XS ms, I2RAX Q st rho msF mo s LB G FF XS ms.

  (* [comment removed for export] *)
  Definition cells0_in (M : itrie region) : Prop :=
    forall rg0 pn p ci c, iget 0%uint63 M = Some rg0 -> iget pn (rg_pages rg0) = Some p -> iget ci (pg_cells p) = Some c ->
      let a := to_Z pn * 4096 + to_Z ci * 8 in
      (exists x, In x (c_xw K) /\ to_Z x = a) \/ a = to_Z (c_errcell K) \/ (exists cc, In (of_Z a, cc) (c_ro K)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable code : itrie finstr.
  Hypothesis Hcode : code_ok asegs code.
  Hypothesis HK : KA_ok = true.
  Hypothesis HHx : asan_rt_hyps_x H.
  Hypothesis Hnw : im_nowr IM.

  Lemma HH : asan_rt_hyps H. Proof. exact (proj1 HHx). Qed.

  Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
  Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn; [tauto|]. rewrite IH. tauto. Qed.

  Lemma outside_map : forall {T} (f : T -> ivl) (l : list T) x,
    outside (map f l) x <-> forall y, In y l -> ~ (fst (f y) <= x < snd (f y)).
  Proof.
    induction l as [|y l IH]; intros x; cbn.
    - split; [intros _ y [] | intros _; exact I].
    - destruct (f y) as [lo hi] eqn:Ef. rewrite IH. split.
      + intros [H1 H2] z [<-|Hz]; [rewrite Ef; cbn; exact H1 | exact (H2 z Hz)].
      + intros Hz. split; [specialize (Hz y (or_introl eq_refl)); rewrite Ef in Hz; exact Hz|].
        intros z Hz'. apply Hz. right. exact Hz'.
  Qed.

  Lemma disjoint_from_app : forall W1 W2 a n, disjoint_from (W1 ++ W2) a n <-> disjoint_from W1 a n /\ disjoint_from W2 a n.
  Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 a n; cbn; [tauto|]. rewrite IH. tauto. Qed.

  Lemma disjoint_from_map : forall {T} (f : T -> ivl) (l : list T) a n,
    disjoint_from (map f l) a n <-> forall y, In y l -> a + n <= fst (f y) \/ snd (f y) <= a.
  Proof.
    induction l as [|y l IH]; intros a n; cbn.
    - split; [intros _ y [] | intros _; exact I].
    - destruct (f y) as [lo hi] eqn:Ef. rewrite IH. split.
      + intros [H1 H2] z [<-|Hz]; [rewrite Ef; cbn; exact H1 | exact (H2 z Hz)].
      + intros Hz. split; [specialize (Hz y (or_introl eq_refl)); rewrite Ef in Hz; exact Hz|].
        intros z Hz'. apply Hz. right. exact Hz'.
  Qed.

  Lemma Forall_app_iff : forall {T} (P : T -> Prop) l1 l2, Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
  Proof. intros. apply Forall_app. Qed.

  (* [comment removed for export] *)
  Lemma HK_parts : forallb xw_cell_ok (c_xw K) = true /\ K_err_ok = true /\ K_pcs_ok = true /\ K_ro_ok = true
                   /\ K_caps_ok = true /\ K_rb_ok = true /\ K_sh0_ok = true.
  Proof. unfold KA_ok in HK. rewrite !andb_true_iff in HK. tauto. Qed.

  Lemma awin_b_spec : forall lo hi, awin_b lo hi = true -> aimg_client_w lo hi /\ 0x5ea840 <= lo /\ hi <= 0xc03570.
  Proof.
    intros lo hi Hb. unfold awin_b in Hb. unfold aimg_client_w. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ALIBC_PGSZ, ATSD0, ATP in *.
    rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in Hb. slia.
  Qed.

  Lemma aconst_okb_spec : forall lo hi, aconst_okb lo hi = true -> aconst_ok (lo, hi).
  Proof.
    intros lo hi Hb. unfold aconst_okb in Hb. rewrite !andb_true_iff, !orb_true_iff, !Z.leb_le in Hb.
    destruct Hb as [[[[[[[[[[[[[[[[K1 K2] K3] K4] K5] K6] K7] K8] K9] K10] K11] K12] K13] K14] K15] K16] K17].
    apply aconst_ok_intro; assumption.
  Qed.

  Lemma HK_xw : forall c, In c (c_xw K) -> xw_cell_ok c = true.
  Proof. intros c Hc. destruct HK_parts as (Hx & _). rewrite forallb_forall in Hx. exact (Hx c Hc). Qed.

  Lemma xw_cell_ok_spec : forall c, xw_cell_ok c = true ->
    to_Z c mod 8 = 0 /\ aimg_client_w (to_Z c) (to_Z c + 8) /\ 0x5ea840 <= to_Z c /\ to_Z c + 8 <= 0xc03570
    /\ aconst_ok (to_Z c, to_Z c + 8)
    /\ (to_Z c + 8 <= AERRNO \/ AERRNO + 4 <= to_Z c).
  Proof.
    intros c Hc. unfold xw_cell_ok in Hc. rewrite !andb_true_iff in Hc. destruct Hc as [[[H8 Hw] Ha] He].
    apply Uint63.eqb_spec in H8. apply (f_equal to_Z) in H8. rewrite to_Z_land7 in H8. change (to_Z 0) with 0 in H8.
    destruct (awin_b_spec _ _ Hw) as (W1 & W2 & W3). pose proof (aconst_okb_spec _ _ Ha) as HA.
    rewrite orb_true_iff, !Z.leb_le in He.
    repeat split; assumption.
  Qed.

  Lemma HK_caps : to_Z (c_cost K) < 2 ^ 60 /\ to_Z (c_cnt K) < 2 ^ 60 /\ to_Z (ka_fsmax A) < 2 ^ 60.
  Proof.
    destruct HK_parts as (_ & _ & _ & _ & Hc & _). unfold K_caps_ok in Hc. rewrite !andb_true_iff in Hc.
    destruct Hc as [[H1 H2] H3]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3. repeat split; assumption.
  Qed.

  Lemma HK_err : to_Z (c_errcell K) + to_Z (c_errbi K) = AERRNO /\ to_Z (c_errcell K) mod 8 = 0 /\ to_Z (c_errbi K) + 4 <= 8
                 /\ aimg_client_w (to_Z (c_errcell K)) (to_Z (c_errcell K) + 8) /\ aconst_ok (to_Z (c_errcell K), to_Z (c_errcell K) + 8)
                 /\ to_Z (c_tp K) = ATP
                 /\ AMALLOC_STACK <= to_Z (c_mstack K) /\ AREALLOC_STACK <= to_Z (c_mstack K) /\ AFREE_STACK <= to_Z (c_mstack K)
                 /\ to_Z (c_mstack K) <= to_Z (c_stack K)
                 /\ to_Z (ka_fstack A) = AFS_STACK /\ to_Z (ka_istack A) = AINTRIN_STACK
                 /\ AFS_STACK <= to_Z (c_stack K) /\ AINTRIN_STACK <= to_Z (c_stack K)
                 /\ to_Z (c_stack K) mod 16 = 0 /\ to_Z (c_stack K) <= 2 ^ 40.
  Proof.
    destruct HK_parts as (_ & HE & _). unfold K_err_ok in HE. rewrite !andb_true_iff in HE.
    destruct HE as [[[[[[[[[[[[[[[He H8] Hbi] Hw] Ha] Htp] Hm1] Hm2] Hm3] Hm4] Hf1] Hf2] Hf3] Hf4] H16] H40].
    apply Z.eqb_eq in He. apply Uint63.eqb_spec in H8. apply (f_equal to_Z) in H8. rewrite to_Z_land7 in H8.
    apply Z.leb_le in Hbi. apply Z.eqb_eq in Htp. apply Z.leb_le in Hm1. apply Z.leb_le in Hm2. apply Z.leb_le in Hm3. apply Z.leb_le in Hm4.
    apply Z.eqb_eq in Hf1. apply Z.eqb_eq in Hf2. apply Z.leb_le in Hf3. apply Z.leb_le in Hf4.
    apply Uint63.eqb_spec in H16. apply (f_equal to_Z) in H16.
    rewrite (i63_land_ones (c_stack K) 15%uint63 4 eq_refl ltac:(slia)) in H16. change (2 ^ 4) with 16 in H16.
    apply Z.leb_le in H40.
    destruct (awin_b_spec _ _ Hw) as (W1 & _). pose proof (aconst_okb_spec _ _ Ha) as HA.
    repeat split; try assumption; try reflexivity.
  Qed.

  Ltac hk_xw c Hc :=
    let X := fresh "Xw" in
    pose proof (xw_cell_ok_spec c (HK_xw c Hc)) as X;
    destruct X as (? & ? & ? & ? & ? & ?); pose proof (i63_range c).

  Ltac hk_err :=
    let E1 := fresh "Eerr" in let E2 := fresh "Eerr8" in let E3 := fresh "Ebi" in let E4 := fresh "Ewin" in let E5 := fresh "Eac" in
    let E6 := fresh "Etp" in let E7 := fresh "Em1" in let E8 := fresh "Em2" in let E9 := fresh "Em3" in let E10 := fresh "Em4" in
    let E11 := fresh "Ef1" in let E12 := fresh "Ef2" in let E13 := fresh "Ef3" in let E14 := fresh "Ef4" in
    let E15 := fresh "Est16" in let E16 := fresh "Est40" in
    destruct HK_err as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16);
    pose proof (i63_range (c_errbi K)); pose proof (i63_range (c_errcell K)); pose proof (i63_range (c_stack K));
    pose proof (i63_range (c_mstack K)).

  Lemma HK_ro : forall a c, In (a, c) (c_ro K) ->
    to_Z a mod 8 = 0 /\ AIMG_LO <= to_Z a /\ to_Z a + 8 <= AIMG_TOP /\ ~ (exists x, In x (c_xw K) /\ x = a) /\ a <> c_errcell K.
  Proof.
    intros a c Hin. destruct HK_parts as (_ & _ & _ & Hro & _). unfold K_ro_ok in Hro.
    rewrite forallb_forall in Hro. specialize (Hro (a, c) Hin). cbn [fst] in Hro. rewrite !andb_true_iff in Hro.
    destruct Hro as [[[[H8 Hlo] Hhi] Hx] He].
    apply Uint63.eqb_spec in H8. apply (f_equal to_Z) in H8. rewrite to_Z_land7 in H8.
    apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. apply negb_true_iff in Hx. apply negb_true_iff in He.
    repeat split; try assumption.
    - intros (x & Hx' & ->). assert (existsb (fun c0 : int => (c0 =? a)%uint63) (c_xw K) = true); [|congruence].
      apply existsb_exists. exists a. split; [exact Hx' | apply Uint63.eqb_refl].
    - intros ->. rewrite Uint63.eqb_refl in He. discriminate.
  Qed.

  Lemma HK_rb : forall b, In b (c_rb K) -> AIMG_LO <= to_Z b < AIMG_TOP.
  Proof.
    intros b Hb. destruct HK_parts as (_ & _ & _ & _ & _ & Hr & _). unfold K_rb_ok in Hr.
    rewrite forallb_forall in Hr. specialize (Hr b Hb). apply andb_true_iff in Hr as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma fold_iset_in : forall (l : list int) k, In k l -> iget k (fold_right (fun b acc => iset b tt acc) iempty l) = Some tt.
  Proof.
    induction l as [|b l IH]; intros k Hk; [destruct Hk|]. cbn [fold_right]. rewrite iget_iset.
    destruct (k =? b)%uint63 eqn:E; [reflexivity|]. destruct Hk as [->|Hk]; [rewrite Uint63.eqb_refl in E; discriminate | exact (IH k Hk)].
  Qed.
  Lemma fold_iset_inv : forall (l : list int) k u, iget k (fold_right (fun b acc => iset b tt acc) iempty l) = Some u -> In k l.
  Proof.
    induction l as [|b l IH]; intros k u Hg; cbn [fold_right] in Hg; [rewrite iget_iempty in Hg; discriminate|].
    rewrite iget_iset in Hg. destruct (k =? b)%uint63 eqn:E; [apply Uint63.eqb_spec in E; left; symmetry; exact E | right; exact (IH k u Hg)].
  Qed.

  Lemma int_add_small : forall (c j : int), to_Z j < 8 -> to_Z c + 8 <= 2 ^ 62 -> to_Z (c + j)%uint63 = to_Z c + to_Z j.
  Proof.
    intros c j Hj Hc. pose proof (i63_range c). pose proof (i63_range j). rewrite Uint63.add_spec. change wB with (2 ^ 63).
    apply Z.mod_small. slia.
  Qed.

  Lemma in_j8 : forall j : int, In j [0; 1; 2; 3; 4; 5; 6; 7]%uint63 -> 0 <= to_Z j < 8.
  Proof. intros j Hj. cbn [In] in Hj. repeat (destruct Hj as [<-|Hj]; [cbn; slia|]). destruct Hj. Qed.

  Lemma j8_in : forall j : Z, 0 <= j < 8 -> In (of_Z j) [0; 1; 2; 3; 4; 5; 6; 7]%uint63.
  Proof.
    intros j Hj. assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by slia.
    cbn [In]. destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; tauto.
  Qed.

  Lemma ro_of_cell : forall a c (j : Z), In (a, c) (c_ro K) -> 0 <= j < 8 ->
    exists k, iget k RO = Some tt /\ to_Z k = to_Z a + j.
  Proof.
    intros a c j Hin Hj. pose proof (HK_ro a c Hin) as (_ & Hlo & Hhi & _). unfold AIMG_LO, AIMG_TOP in *.
    exists (a + of_Z j)%uint63. split.
    - unfold RO, ro_of. apply fold_iset_in. unfold ro_bytes. apply in_or_app. left.
      apply in_flat_map. exists (a, c). split; [exact Hin|]. cbn [fst]. apply in_map. apply j8_in. exact Hj.
    - rewrite int_add_small; rewrite ?toZ_of_Z_small by slia; slia.
  Qed.
  Lemma ro_of_rb : forall b, In b (c_rb K) -> iget b RO = Some tt.
  Proof. intros b Hb. unfold RO, ro_of. apply fold_iset_in. unfold ro_bytes. apply in_or_app. right. exact Hb. Qed.
  Lemma ro_of_range : forall k u, iget k RO = Some u -> AIMG_LO <= to_Z k < AIMG_TOP.
  Proof.
    intros k u Hg. unfold RO, ro_of in Hg. apply fold_iset_inv in Hg. unfold ro_bytes in Hg. apply in_app_or in Hg as [Hg|Hg].
    - apply in_flat_map in Hg as ([a c] & Hin & Hk). cbn [fst] in Hk. apply in_map_iff in Hk as (j & <- & Hj).
      pose proof (HK_ro a c Hin) as (_ & Hlo & Hhi & _). pose proof (in_j8 j Hj). unfold AIMG_LO, AIMG_TOP in *. rewrite int_add_small by slia. slia.
    - exact (HK_rb k Hg).
  Qed.

  Lemma rb_addr_dec : forall a, rb_addr a \/ ~ rb_addr a.
  Proof.
    intros a. unfold rb_addr. induction (c_rb K) as [|b l IH]; [right; intros (b & [] & _)|].
    destruct (Z.eq_dec (to_Z b) a) as [E|NE]; [left; exists b; split; [left; reflexivity | exact E]|].
    destruct IH as [(b' & Hb' & E')|IH]; [left; exists b'; split; [right; exact Hb' | exact E']|].
    right. intros (b' & [<-|Hb'] & E'); [exact (NE E') | apply IH; exists b'; split; assumption].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma option_byte_eq_dec : forall (x y : option byte), x = y \/ x <> y.
  Proof.
    intros [x|] [y|]; try (right; discriminate); [|left; reflexivity].
    destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned y)) as [E|NE].
    - left. f_equal. apply bv_eq. exact E.
    - right. intros E. apply NE. injection E as ->. reflexivity.
  Qed.

  Lemma ablock_of_G : forall Q st rho msF mo s LB G FF XS ms g,
    I2RAX Q st rho msF mo s LB G FF XS ms -> In g G -> ablock_range H (g_addr g) (to_Z (g_size g)).
  Proof.
    intros Q st rho msF mo s LB G FF XS ms g X Hg.
    pose proof (proj1 (Forall_forall _ _) (r_Gin _ _ _ _ _ _ _ _ _ _ _ X) g Hg) as (Hin & _).
    exact (ah_blocks H HH _ _ _ _ (r_heap _ _ _ _ _ _ _ _ _ _ _ X) Hin).
  Qed.

  Lemma aframe_of_FF : forall Q st rho msF mo s LB G FF XS ms f,
    I2RAX Q st rho msF mo s LB G FF XS ms -> In f FF ->
    aframe_range H (to_Z (f_k f)) (f_ff f) (f_fp f) /\ afsb_ok H.
  Proof.
    intros Q st rho msF mo s LB G FF XS ms f X Hf.
    destruct (ah_RFS_range H HH _ _ (r_rfs _ _ _ _ _ _ _ _ _ _ _ X)) as [Hfsb Hfr].
    specialize (Hfr (ff_of f) ltac:(unfold LF_of; apply in_or_app; left; apply in_map; exact Hf)).
    cbn [ff_of ff_class ff_addr ff_flag fst snd] in Hfr. split; [exact Hfr | exact Hfsb].
  Qed.

  Lemma adr_wa : forall rho t A' z, rho t = wa A' -> 0 <= A' -> 0 <= z -> A' + z < 2 ^ 64 ->
    bv_unsigned (adr rho t z) = A' + z.
  Proof.
    intros rho t A' z Ht HA Hz Hlt. unfold adr, wa. rewrite Ht, bv_add_unsigned, !Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_small A') by slia. rewrite (Z.mod_small z) by slia. apply Z.mod_small. slia.
  Qed.

  Lemma adr_0 : forall rho z, rho 0%uint63 = Z_to_bv 64 0 -> 0 <= z < 2 ^ 64 -> bv_unsigned (adr rho 0%uint63 z) = z.
  Proof. intros rho z H0 Hz. rewrite (adr_wa rho 0%uint63 0 z); [slia | exact H0 | slia | slia | slia]. Qed.

  Lemma adr_lin : forall rho t z, 0 <= z -> bv_unsigned (rho t) + z < 2 ^ 64 -> bv_unsigned (adr rho t z) = bv_unsigned (rho t) + z.
  Proof.
    intros rho t z Hz Hlt. pose proof (bv_unsigned_in_range _ (rho t)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    unfold adr. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_small z) by slia. apply Z.mod_small. slia.
  Qed.

  (* [comment removed for export] *)
  Lemma region_of_addr_unique : forall rho M m t t' rg rg' (o o' : Z),
    mem_ok asegs IM rho M m -> iget t M = Some rg -> iget t' M = Some rg' ->
    to_Z (rg_lo rg) <= o < to_Z (rg_len rg) -> to_Z (rg_lo rg') <= o' < to_Z (rg_len rg') ->
    adr rho t o = adr rho t' o' -> t = t'.
  Proof.
    intros rho M m t t' rg rg' o o' [Hreg Hsep] Ht Ht' Ho Ho' E.
    destruct (Uint63.eqb t t') eqn:Et; [apply Uint63.eqb_spec in Et; exact Et|]. exfalso.
    assert (NE : t <> t') by (intros ->; rewrite Uint63.eqb_refl in Et; discriminate).
    destruct (Hreg t rg Ht) as [(_ & _ & Hb & _) _]. destruct (Hreg t' rg' Ht') as [(_ & _ & Hb' & _) _].
    pose proof (i63_range (rg_lo rg)). pose proof (i63_range (rg_lo rg')).
    apply (f_equal bv_unsigned) in E. rewrite (adr_lin rho t o), (adr_lin rho t' o') in E by slia.
    destruct (Hsep t t' rg rg' NE Ht Ht') as [S|S]; slia.
  Qed.

  (* [comment removed for export] *)
  Definition segW (Q : i2aenv) (G : list gblk) (FF : list gframe) : list ivl :=
    map (fun c : int => (to_Z c, to_Z c + 8)) (c_xw K)
    ++ [(to_Z (c_errcell K), to_Z (c_errcell K) + 8)]
    ++ [(q_sp0 Q - to_Z (c_stack K), q_sp0 Q)]
    ++ map (fun g => (g_addr g, g_addr g + to_Z (g_size g))) G
    ++ map (fun f => (f_ff f, f_ff f + AsIface.fsz (to_Z (f_k f)))) FF
    ++ map (fun f => (sh (f_ff f), sh (f_ff f) + fshn (to_Z (f_k f)))) FF.

  Lemma fsz_eq : forall k : int, 0 <= to_Z k <= 6 -> to_Z (I2RunA.fsz k) = AsIface.fsz (to_Z k).
  Proof.
    intros k Hk. unfold I2RunA.fsz, AsIface.fsz. rewrite Uint63.lsl_spec. change (to_Z 64) with 64. change wB with (2 ^ 63).
    pose proof (Z.pow_le_mono_r 2 (to_Z k) 6 ltac:(slia) ltac:(slia)) as Hp. change (2 ^ 6) with 64 in Hp.
    pose proof (Z.pow_pos_nonneg 2 (to_Z k) ltac:(slia) ltac:(slia)).
    rewrite Z.mod_small; slia.
  Qed.
  Lemma fsz_fshn : forall k, 0 <= k -> fshn k = nsh (AsIface.fsz k) /\ AsIface.fsz k = 8 * fshn k.
  Proof. intros k Hk. unfold fshn, nsh, AsIface.fsz. pose proof (Z.pow_pos_nonneg 2 k ltac:(slia) Hk). split; [Z.div_mod_to_equations; slia | slia]. Qed.

  Lemma frame_al8 : forall k ff fp, aframe_range H k ff fp -> ff mod 8 = 0.
  Proof.
    intros k ff fp (K1 & K2 & K3 & K4 & K5). pose proof (fsz_pos k ltac:(slia)) as P.
    apply Z.mod_divide; [slia|]. apply (Z.divide_trans 8 (AsIface.fsz k) ff).
    - exists (8 * 2 ^ k). unfold AsIface.fsz. slia.
    - apply Z.mod_divide; [slia | exact K4].
  Qed.

  (* [comment removed for export] *)
  Lemma segW_ok : forall Q st rho msF mo s LB G FF XS ms,
    I2RAX Q st rho msF mo s LB G FF XS ms ->
    Forall (aclient_write_ok H LB) (segW Q G FF)
    /\ Forall (afs_write_ok H (LF_of Q FF)) (segW Q G FF)
    /\ Forall aconst_ok (segW Q G FF)
    /\ Forall stack0_ok (segW Q G FF)
    /\ Forall (fun iv : Z * Z => snd iv <= q_sp0 Q) (segW Q G FF).
  Proof.
    intros Q st rho msF mo s LB G FF XS ms X.
    pose proof (r_lo _ _ _ _ _ _ _ _ _ _ _ X) as (Hal & Hl2 & HB & _ & _ & HB64 & _).
    pose proof (ah_fsb H HH _ _ _ (r_heap _ _ _ _ _ _ _ _ _ _ _ X)) as (F1 & F2 & F3 & F4).
    assert (Gfacts : forall g, In g G -> ablock_range H (g_addr g) (to_Z (g_size g)) /\ In (g_id g, g_addr g, to_Z (g_size g)) LB).
    { intros g Hg. split; [exact (ablock_of_G _ _ _ _ _ _ _ _ _ _ _ _ X Hg)|].
      exact (proj1 (proj1 (Forall_forall _ _) (r_Gin _ _ _ _ _ _ _ _ _ _ _ X) g Hg)). }
    assert (Ffacts : forall f, In f FF -> (aframe_range H (to_Z (f_k f)) (f_ff f) (f_fp f) /\ 64 <= AsIface.fsz (to_Z (f_k f))) /\ In (ff_of f) (LF_of Q FF)).
    { intros f Hf. pose proof (proj1 (aframe_of_FF _ _ _ _ _ _ _ _ _ _ _ _ X Hf)) as AF. split; [split; [exact AF|]|].
      - apply fsz_pos. destruct AF as (K1 & _). slia.
      - unfold LF_of. apply in_or_app. left. apply in_map. exact Hf. }
    acb. pose proof (i63_range (c_stack K)). unfold segW. repeat split.
    - (* [comment removed for export] *)
      rewrite !Forall_app_iff. repeat split.
      + apply Forall_map. apply Forall_forall. intros c Hc. hk_xw c Hc. right. left. cbn [fst snd]. assumption.
      + constructor; [|constructor]. right. left. cbn [fst snd]. hk_err. assumption.
      + constructor; [|constructor]. left. cbn [fst]. slia.
      + apply Forall_map. apply Forall_forall. intros g Hg. right. right. left. cbn [fst snd].
        exists (g_id g, g_addr g, to_Z (g_size g)). split; [exact (proj2 (Gfacts g Hg))|]. cbn [blk_addr blk_size fst snd]. slia.
      + apply Forall_map. apply Forall_forall. intros f Hf. destruct (proj1 (Ffacts f Hf)) as [(K1 & K2 & K3 & K4 & K5) Kp].
        right. right. right. right. left. cbn [fst snd]. unfold AFS_HDR in *. slia.
      + apply Forall_map. apply Forall_forall. intros f Hf. destruct (proj1 (Ffacts f Hf)) as [(K1 & K2 & K3 & K4 & K5) Kp].
        right. right. right. right. right. left. cbn [fst snd].
        pose proof (fsz_fshn (to_Z (f_k f)) ltac:(slia)) as [E1 E2]. unfold AFS_HDR in *.
        split; [apply sh_mono; slia|]. rewrite E1. assert (TMP : f_ff f + AsIface.fsz (to_Z (f_k f)) + 7 <= as_FSB H + AFS_SIZE + 7) by slia. pose proof (sh_mono _ _ TMP).
        unfold nsh, sh in *. Z.div_mod_to_equations. slia.
    - (* [comment removed for export] *)
      rewrite !Forall_app_iff. unfold afs_write_ok. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP. repeat split.
      + apply Forall_map. apply Forall_forall. intros c Hc. hk_xw c Hc. left. cbn [fst snd].
        unfold aimg_client_w, ATLS_PRIV_LO, ATLS_PRIV_HI, ALIBC_PGSZ, ATSD0, ATP, AIMG_TOP in *. slia.
      + constructor; [|constructor]. left. cbn [fst snd]. hk_err.
        unfold aimg_client_w, ATLS_PRIV_LO, ATLS_PRIV_HI, ALIBC_PGSZ, ATSD0, ATP, AIMG_TOP in *. slia.
      + constructor; [|constructor]. left. cbn [fst snd]. slia.
      + apply Forall_map. apply Forall_forall. intros g Hg. left. cbn [fst snd].
        destruct (proj1 (Gfacts g Hg)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7). unfold AIMG_TOP in *. slia.
      + apply Forall_map. apply Forall_forall. intros f Hf. right. exists (ff_of f). split; [exact (proj2 (Ffacts f Hf))|].
        cbn [ff_of ff_addr ff_class fst snd]. slia.
      + apply Forall_map. apply Forall_forall. intros f Hf. left. cbn [fst snd].
        destruct (proj1 (Ffacts f Hf)) as [(K1 & K2 & K3 & K4 & K5) Kp]. pose proof (fsz_fshn (to_Z (f_k f)) ltac:(slia)) as [E1 E2].
        pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE (f_ff f) (AsIface.fsz (to_Z (f_k f))) F4) as D.
        pose proof (aapp_bounds _ _ F4 ltac:(unfold AFS_SIZE; slia)) as (Q1 & Q2 & Q3 & Q4 & Q5).
        unfold AFS_HDR, AFS_SIZE, AAPP_HI, AIMG_TOP in *. rewrite E1.
        split; [apply D; slia|]. right. pose proof (sh_above_image (f_ff f) ltac:(slia)). unfold AIMG_TOP in *. slia.
    - (* [comment removed for export] *)
      rewrite !Forall_app_iff. repeat split.
      + apply Forall_map. apply Forall_forall. intros c Hc. hk_xw c Hc. assumption.
      + constructor; [|constructor]. hk_err. assumption.
      + constructor; [|constructor]. apply aconst_ok_high; [|right; left; slia].
        pose proof (sh_below_aceil 0xc04000 ltac:(unfold AAPP_HI; slia)). unfold AIMG_TOP. slia.
      + apply Forall_map. apply Forall_forall. intros g Hg. destruct (proj1 (Gfacts g Hg)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
        apply aconst_ok_intro; cbn [fst snd]; aapp_unfold; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL,
          ACANPOISON_CELL, AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, ASHADOW_BASE in *; slia.
      + apply Forall_map. apply Forall_forall. intros f Hf. destruct (proj1 (Ffacts f Hf)) as [(K1 & K2 & K3 & K4 & K5) Kp].
        apply aconst_ok_intro; cbn [fst snd]; aapp_unfold; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL,
          ACANPOISON_CELL, AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, ASHADOW_BASE, AFS_HDR, AFS_SIZE in *; slia.
      + apply Forall_map. apply Forall_forall. intros f Hf. destruct (proj1 (Ffacts f Hf)) as [(K1 & K2 & K3 & K4 & K5) Kp].
        pose proof (fsz_fshn (to_Z (f_k f)) ltac:(slia)) as [E1 E2]. pose proof (sh_above_image (f_ff f) ltac:(aapp_unfold; unfold AFS_HDR in *; slia)).
        apply aconst_ok_intro; cbn [fst snd]; aapp_unfold; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL,
          ACANPOISON_CELL, AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, ASHADOW_BASE, AFS_HDR, AFS_SIZE in *; slia.
    - (* [comment removed for export] *)
      rewrite !Forall_app_iff. repeat split.
      + apply Forall_map. apply Forall_forall. intros c Hc. hk_xw c Hc. unfold stack0_ok. right. cbn [fst snd].
        assert (TMP : 0xc04000 <= aceil) by slia.
        pose proof (sh_mono _ _ TMP). unfold sh, ASHADOW_BASE in *. slia.
      + constructor; [|constructor]. unfold stack0_ok. right. cbn [fst snd]. hk_err. unfold aimg_client_w, ATLS_PRIV_LO, ATLS_PRIV_HI, ALIBC_PGSZ, ATSD0, ATP in *.
        assert (TMP : 0xc04000 <= aceil) by slia.
        pose proof (sh_mono _ _ TMP). unfold sh, ASHADOW_BASE in *. slia.
      + constructor; [|constructor]. unfold stack0_ok. left. cbn [fst snd]. unfold AHI_LO. slia.
      + apply Forall_map. apply Forall_forall. intros g Hg. destruct (proj1 (Gfacts g Hg)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
        apply (stack0_ok_aapp _ _ _ _ R7); slia.
      + apply Forall_map. apply Forall_forall. intros f Hf. destruct (proj1 (Ffacts f Hf)) as [(K1 & K2 & K3 & K4 & K5) Kp].
        apply (stack0_ok_aapp _ _ _ _ F4); unfold AFS_HDR in *; slia.
      + apply Forall_map. apply Forall_forall. intros f Hf. destruct (proj1 (Ffacts f Hf)) as [(K1 & K2 & K3 & K4 & K5) Kp].
        unfold stack0_ok. right. cbn [fst snd]. pose proof (fsz_fshn (to_Z (f_k f)) ltac:(slia)) as [E1 E2]. rewrite E1.
        pose proof (frame_al8 _ _ _ (conj K1 (conj K2 (conj K3 (conj K4 K5))))) as A8.
        assert (TMP : f_ff f + AsIface.fsz (to_Z (f_k f)) <= aceil) by (unfold AFS_HDR in *; slia).
        clear - A8 TMP ACEILB Kp. unfold nsh, sh in *. Z.div_mod_to_equations. slia.
    - (* [comment removed for export] *)
      rewrite !Forall_app_iff. repeat split.
      + apply Forall_map. apply Forall_forall. intros c Hc. hk_xw c Hc. cbn [snd]. slia.
      + constructor; [|constructor]. cbn [snd]. hk_err. unfold aimg_client_w, ATLS_PRIV_LO, ATLS_PRIV_HI, ALIBC_PGSZ, ATSD0, ATP in *. slia.
      + constructor; [|constructor]. cbn [snd]. slia.
      + apply Forall_map. apply Forall_forall. intros g Hg. destruct (proj1 (Gfacts g Hg)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7). cbn [snd]. slia.
      + apply Forall_map. apply Forall_forall. intros f Hf. destruct (proj1 (Ffacts f Hf)) as [(K1 & K2 & K3 & K4 & K5) Kp]. cbn [snd]. unfold AFS_HDR in *. slia.
      + apply Forall_map. apply Forall_forall. intros f Hf. destruct (proj1 (Ffacts f Hf)) as [(K1 & K2 & K3 & K4 & K5) Kp]. cbn [snd].
        pose proof (fsz_fshn (to_Z (f_k f)) ltac:(slia)) as [E1 E2]. rewrite E1.
        pose proof (sh_below_aceil (f_ff f + AsIface.fsz (to_Z (f_k f)) + 7) ltac:(aapp_unfold; unfold AFS_HDR, AFS_SIZE in *; slia)).
        unfold nsh, sh in *. Z.div_mod_to_equations. slia.
  Qed.
  (* [comment removed for export] *)
  Lemma ro_region_sh : forall p n, ro_region (sh_region false p n).
  Proof.
    intros p n. split; [reflexivity|]. intros pn pg Hp. unfold sh_region in Hp. cbn [rg_pages] in Hp.
    rewrite iget_iset, iget_iempty in Hp. destruct (pn =? 0)%uint63; [injection Hp as <-; reflexivity | discriminate].
  Qed.
  Lemma ro_region_flag : ro_region flag_region.
  Proof.
    split; [reflexivity|]. intros pn pg Hp. unfold flag_region in Hp. cbn [rg_pages] in Hp.
    rewrite iget_iset, iget_iempty in Hp. destruct (pn =? 0)%uint63; [injection Hp as <-; reflexivity | discriminate].
  Qed.
  Lemma abs_pages_shape : forall cells pn p, iget pn (abs_pages cells) = Some p -> pg_wr p = false /\ pg_kind p = PKUnk.
  Proof.
    induction cells as [|ac cells IH]; intros pn p Hp; cbn [abs_pages fold_right] in Hp.
    - rewrite iget_iempty in Hp. discriminate.
    - fold (abs_pages cells) in Hp. rewrite iget_iset in Hp. destruct (pn =? (fst ac >> 12))%uint63.
      + injection Hp as <-. split; reflexivity.
      + exact (IH pn p Hp).
  Qed.
  Lemma ro_region_abs : forall lo len cells, ro_region (abs_region lo len cells).
  Proof.
    intros lo len cells. split; [reflexivity|]. intros pn pg Hp. unfold abs_region in Hp. cbn [rg_pages] in Hp.
    exact (proj1 (abs_pages_shape _ _ _ Hp)).
  Qed.
  Lemma page_at_ro : forall rg t pn p, ro_region rg -> t <> 0%uint63 -> page_at IM rg t pn = Some p ->
    iget pn (rg_pages rg) = Some p /\ pg_wr p = false.
  Proof.
    intros rg t pn p [Hd Hw] Ht Hp. unfold page_at in Hp. destruct (iget pn (rg_pages rg)) as [p0|] eqn:E.
    - injection Hp as <-. split; [reflexivity | exact (Hw _ _ E)].
    - destruct (t =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; congruence|]. rewrite Hd in Hp. discriminate.
  Qed.
  Lemma page_at_expl : forall rg t pn p, iget pn (rg_pages rg) = Some p -> page_at IM rg t pn = Some p.
  Proof. intros rg t pn p Hp. unfold page_at. rewrite Hp. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma page_at_0_wr : forall rg pn p, page_at IM rg 0%uint63 pn = Some p -> pg_wr p = true -> rg_dflt rg = None ->
    iget pn (rg_pages rg) = Some p.
  Proof.
    intros rg pn p Hp Hw Hd. unfold page_at in Hp. destruct (iget pn (rg_pages rg)) as [p0|] eqn:E; [congruence|].
    change ((0 =? 0)%uint63) with true in Hp. cbv iota in Hp.
    destruct (find_seg IM (pn << 12)%uint63) as [sg|] eqn:Hsg.
    - injection Hp as <-. cbn in Hw. rewrite (Hnw _ _ Hsg) in Hw. discriminate.
    - rewrite Hd in Hp. discriminate.
  Qed.

  Theorem seg_sound : forall Q st rho msF mo F' r cnt,
    fx_run IM code RO no_bp 40 (a_F st) = (F', r, cnt) ->
    I2RA Q st rho msF mo ->
    cells0_in (f_mem F') ->
    as_SR H (fun c' => I2RA Q (awith_F st F') rho (cfg_ms c') (cfg_model c')) (mkCfg msF mo).
  Proof.
    intros Q st rho msF mo F' r cnt Hrun (s & LB & G & FF & XS & ms & X) Hc0.
    pose proof X as X'.
    destruct X' as [r_vis0 r_Rn0 r_canon0 r_fregs0 r_fcsr0 r_rom0 r_rho00 r_rho10 r_rho20 r_rho30 r_agree0 r_n1 r_akrel0 r_mpres0
                    r_heap0 r_rfs0 r_aconst0 r_stack00 r_chain0 r_CH00 r_s0v0 r_pfo0 r_AL1 r_AL00
                    r_G0 r_Gin0 r_Gnodup0 r_Gtnd0 r_Gnew0 r_Gstk0
                    r_FF0 r_FFin0 r_FFnd0 r_FFtnd0 r_Tsep0 r_FFlen0 r_XS0
                    r_dom0 r_r00 r_r10 r_r20 r_r30 r_ro0 r_inb0 r_kinds0
                    r_cost0 r_cnt0 r_stk0 r_lo0 r_auxv0 r_inv0 r_err0 r_sh00 r_LB1 r_LB0h0 r_named1 r_LBsub0 r_frame0 r_FFstk0].
    destruct (fx_run_pkg asegs IM code RO Hcode (a_n st) rho no_bp 40 (a_F st) F' r cnt ms ltac:(slia) Hrun r_rho00 r_Rn0 r_ro0 r_canon0)
      as (ms' & Hsteps & Hms & HRn' & _ & Hrom & Hfr & Hfc & Hmrel & Hcell & Hrof & Hro' & Hcan').
    destruct (fx_run_Rn asegs IM code RO Hcode (a_n st) rho no_bp 40 (a_F st) F' r cnt ms ltac:(slia) Hrun r_rho00 r_Rn0)
      as (ms'' & Hsteps' & _ & _ & Hclf & _ & _).
    rewrite Hsteps in Hsteps'. injection Hsteps' as <-.
    assert (Hag : agree (a_n st) rho rho) by (split; [exact r_rho00 | intros; reflexivity]).
    pose proof (r_Rn0 rho Hag) as HR. pose proof (HRn' rho Hag) as HR'.
    destruct (fx_run_shapeA IM code RO asegs rho r_rho00 Hcode Hnw no_bp 40 (a_F st) F' r cnt ltac:(slia) Hrun ms HR)
      as [(Hinb' & Hdf' & Hku') Hp0]; [split; [exact r_inb0 | split; [intros rg0 H0; destruct r_r00 as (rg0_ & H0_ & _ & _ & Hd & _); congruence | exact r_kinds0]]|].
    pose proof (fx_run_geom IM code RO no_bp 40 (a_F st) F' r cnt Hrun) as Hgeom.
    pose proof (fx_run_ro_kept IM code RO no_bp 40 (a_F st) F' r cnt) as Hrok.
    eapply (ah_lift H HH (fun ms'' => ms'' = ms')); [exact r_akrel0 | exact r_vis0 | exists ms'; split; [exact Hms | reflexivity] |].
    intros msF' mo' Hak' Hmp' Hvis'. apply (ah_done H HH). cbn [cfg_ms cfg_model].
    (* [comment removed for export] *)
    set (W := segW Q G FF).
    destruct (segW_ok _ _ _ _ _ _ _ _ _ _ _ X) as (HWc & HWf & HWa & HWs & HWsp). fold W in HWc, HWf, HWa, HWs, HWsp.
    pose proof (r_lo0) as (Hal & Hl2 & HB & Hsp16 & Hsp32 & HB64 & Hshi). acb. pose proof (i63_range (c_stack K)) as Hcs.
    assert (HW : munch W (ms_mem ms) (ms_mem ms')).
    { intros x Hout.
      destruct (option_byte_eq_dec (ms_mem ms' x) (ms_mem ms x)) as [E|NE]; [exact E|]. exfalso. apply NE.
      apply Hclf. intros (t & rg & pn & p & j & Ht & Hpn & Hpat & Hwr & Hj & Hjlen & Ex).
      unfold W, segW in Hout. rewrite !outside_app in Hout. destruct Hout as (Oxw & Oerr & Ostk & Oblk & Off & Ofsh).
      cbn [outside] in Oerr, Ostk. destruct Oerr as [Oerr _]. destruct Ostk as [Ostk _].
      pose proof (i63_range pn).
      destruct (r_dom0 t rg Ht) as [-> | [-> | [-> | [-> | [Hb | [Hbs | [Hf | [Hfs | Hfl]]]]]]]].
      - (* [comment removed for export] *)
        destruct r_r00 as (rg0 & Hrg0 & Hlo0 & Hlen0 & Hd0 & Hpg0). rewrite Hrg0 in Ht. injection Ht as <-.
        pose proof (page_at_0_wr _ _ _ Hpat Hwr Hd0) as Hpex.
        destruct (proj1 (R_mem _ _ _ _ _ HR) 0%uint63 rg0 Hrg0) as [_ Hpages]. destruct (Hpages pn p Hpn Hpat) as (_ & Hlo0' & _).
        apply NE. apply Hcell. intros (t' & rg' & pn' & p' & ci' & Ht' & Hp' & Hci' & j' & Hj' & Hjlen' & Ex').
        pose proof (i63_range pn'). pose proof (i63_range ci').
        destruct (iget ci' (pg_cells p')) as [c'|] eqn:Hc'; [|exact (Hci' eq_refl)].
        destruct (Hinb' t' rg' pn' p' ci' c' Ht' Hp' Hc') as (Hlen' & Hci512 & _).
        (* [comment removed for export] *)
        pose proof (Hgeom 0%uint63) as Hg0. rewrite Hrg0 in Hg0. destruct (iget 0%uint63 (f_mem F')) as [rg0'|] eqn:E0'; [|destruct Hg0].
        destruct Hg0 as (Hl0 & Hn0 & _).
        destruct (proj1 (R_mem _ _ _ _ _ HR') t' rg' Ht') as [(Hrt1 & Hrt2 & _) Hpages']. 
        destruct (Hpages' pn' p' ltac:(slia) (page_at_expl _ t' _ _ Hp')) as (_ & Hlo' & _).
        assert (Et' : 0%uint63 = t').
        { apply (region_of_addr_unique rho (f_mem F') (ms_mem ms') 0%uint63 t' rg0' rg' (to_Z pn * 4096 + j) (to_Z pn' * 4096 + to_Z ci' * 8 + j')
                   (R_mem _ _ _ _ _ HR') E0' Ht'); [rewrite Hl0, Hn0; slia | slia | rewrite <- Ex, <- Ex'; reflexivity]. }
        subst t'. rewrite E0' in Ht'. injection Ht' as <-.
        rewrite Hn0, Hlen0 in Hlen'.
        destruct (Hc0 rg0' pn' p' ci' c' E0' Hp' Hc') as [(xc & Hxin & Hxc) | [Herr | (cc & Hcc)]].
        + apply (proj1 (outside_map _ _ _) Oxw xc Hxin). cbn [fst snd]. hk_xw xc Hxin.
          rewrite Ex', (adr_0 rho _ r_rho00) by slia. slia.
        + apply Oerr. hk_err. unfold AERRNO, ATP in *. rewrite Ex', (adr_0 rho _ r_rho00) by slia. slia.
        + exfalso. apply NE. apply Hrof. pose proof (HK_ro _ _ Hcc) as (_ & Hlo & Hhi & _). unfold AIMG_LO, AIMG_TOP in *.
          rewrite toZ_of_Z_small in Hlo, Hhi by slia.
          destruct (ro_of_cell _ _ j' Hcc Hj') as (k & Hk & Ek). rewrite toZ_of_Z_small in Ek by slia.
          exists k, tt. split; [exact Hk|].
          rewrite Ek, Ex'. apply bv_eq. rewrite (adr_0 rho _ r_rho00) by slia.
          rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by slia. reflexivity.
      - (* [comment removed for export] *)
        destruct r_r10 as (rg1 & Hrg1 & Hlo1 & Hlen1 & _). rewrite Hrg1 in Ht. injection Ht as <-.
        rewrite Hlen1 in Hjlen. apply Ostk. destruct r_stk0 as (_ & Hsp & _).
        rewrite Ex, (adr_wa rho 1%uint63 (q_sp0 Q - to_Z (c_stack K)) _ r_rho10) by slia. slia.
      - (* [comment removed for export] *)
        rewrite r_r20 in Ht. injection Ht as <-.
        destruct (page_at_ro _ 2%uint63 _ _ (ro_region_sh 1%uint63 (c_stack K)) ltac:(intros E; discriminate E) Hpat) as [_ Hw]. congruence.
      - (* [comment removed for export] *)
        rewrite r_r30 in Ht. injection Ht as <-.
        destruct (page_at_ro _ 3%uint63 _ _ (ro_region_abs _ _ _) ltac:(intros E; discriminate E) Hpat) as [_ Hw]. congruence.
      - (* [comment removed for export] *)
        apply in_map_iff in Hb as (g & <- & Hg).
        pose proof (proj1 (Forall_forall _ _) r_Gin0 g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & _) & _).
        rewrite Hgg in Ht. injection Ht as <-. rewrite Hleng in Hjlen.
        apply (proj1 (outside_map _ _ _) Oblk g Hg). cbn [fst snd].
        pose proof (ablock_of_G _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (R1 & R2 & R3 & R4 & R5 & _).
        rewrite Ex, (adr_wa rho (g_tag g) (g_addr g) _ Hrg) by slia. slia.
      - (* [comment removed for export] *)
        apply in_map_iff in Hbs as (g & <- & Hg).
        pose proof (proj1 (Forall_forall _ _) r_Gin0 g Hg) as (_ & _ & _ & Htg1 & Htg2 & _ & Hsh). destruct (Hsh rg Ht) as (-> & _).
        pose proof (i63_range (g_tag g)). destruct r_n1 as [_ Hn60].
        destruct (page_at_ro _ (g_tag g + 1)%uint63 _ _ (ro_region_sh (g_tag g) (g_size g)) ltac:(intros E; apply (f_equal to_Z) in E; rewrite Uint63.add_spec in E; change (to_Z 1%uint63) with 1 in E; change (to_Z 0%uint63) with 0 in E; change wB with (2^63) in E; rewrite Z.mod_small in E by slia; slia) Hpat) as [_ Hw]. congruence.
      - (* [comment removed for export] *)
        apply in_map_iff in Hf as (f & <- & Hf).
        pose proof (proj1 (Forall_forall _ _) r_FFin0 f Hf) as (Hr0 & Hr1 & Hr2 & Hk & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & _) & _).
        rewrite Hgf in Ht. injection Ht as <-. rewrite Hlenf, (fsz_eq _ Hk) in Hjlen.
        apply (proj1 (outside_map _ _ _) Off f Hf). cbn [fst snd].
        destruct (aframe_of_FF _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2 & K3 & K4 & K5) (F1 & F2 & F3 & F4)].
        clear - Ex Hr0 Hj Hjlen K1 K2 K3 K4 K5 F1 F2 F3 F4 ACEILB.
        pose proof (fsz_pos (to_Z (f_k f)) ltac:(slia)). pose proof (i63_range pn).
        assert (B : 0 <= f_ff f /\ f_ff f + AsIface.fsz (to_Z (f_k f)) < 2 ^ 64) by (aapp_unfold; unfold AFS_HDR, AFS_SIZE in *; slia).
        rewrite Ex, (adr_wa rho (f_tag f) (f_ff f) _ Hr0) by slia. slia.
      - (* [comment removed for export] *)
        apply in_map_iff in Hfs as (f & <- & Hf).
        pose proof (proj1 (Forall_forall _ _) r_FFin0 f Hf) as (Hr0 & Hr1 & Hr2 & Hk & Htg1 & Htg2 & _ & (rgs & Hgs & Hlos & Hlens & _) & _).
        rewrite Hgs in Ht. injection Ht as <-. rewrite Hlens in Hjlen.
        apply (proj1 (outside_map _ _ _) Ofsh f Hf). cbn [fst snd].
        destruct (aframe_of_FF _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2 & K3 & K4 & K5) (F1 & F2 & F3 & F4)].
        clear - Ex Hr1 Hj Hjlen Hk K1 K2 K3 K4 K5 F1 F2 F3 F4 ACEILB.
        pose proof (fsz_fshn (to_Z (f_k f)) ltac:(slia)) as [E1 E2]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(slia)). pose proof (i63_range pn).
        assert (B : 0 <= f_ff f < AAPP_HI) by (aapp_unfold; unfold AFS_HDR, AFS_SIZE in *; slia).
        pose proof (sh_below_aceil (f_ff f) B). pose proof (sh_above_image (f_ff f) ltac:(slia)).
        rewrite Ex, (adr_wa rho (f_tag f + 1)%uint63 (sh (f_ff f)) _ Hr1) by (unfold AIMG_TOP in *; slia). slia.
      - (* [comment removed for export] *)
        apply in_map_iff in Hfl as (f & <- & Hf).
        pose proof (proj1 (Forall_forall _ _) r_FFin0 f Hf) as (_ & _ & _ & _ & Htg1 & Htg2 & _ & _ & Hflg & _).
        rewrite Hflg in Ht. injection Ht as <-.
        pose proof (i63_range (f_tag f)). destruct r_n1 as [_ Hn60].
        destruct (page_at_ro _ (f_tag f + 2)%uint63 _ _ ro_region_flag ltac:(intros E; apply (f_equal to_Z) in E; rewrite Uint63.add_spec in E; change (to_Z 2%uint63) with 2 in E; change (to_Z 0%uint63) with 0 in E; change wB with (2^63) in E; rewrite Z.mod_small in E by slia; slia) Hpat) as [_ Hw]. congruence. }
    (* [comment removed for export] *)
    destruct Hmrel as (Hwm & Hinv' & Hrd).
    destruct (client_frame H HH s LB (LF_of Q FF) (q_B Q) W _ _ r_heap0 r_rfs0 r_aconst0 r_auxv0 HW Hwm HWc HWf HWa) as (Hheap' & Hrfs' & Hac' & Haux').
    pose proof (stack0_transport W _ _ _ _ r_stack00 HW Hwm HWs) as Hst0'.
    assert (Hdisj_hi : forall a n, q_sp0 Q <= a -> disjoint_from W a n).
    { intros a n Ha. clear - HWsp Ha. induction W as [|[lo hi] W IH]; cbn; [exact I|].
      pose proof (Forall_inv HWsp) as H1. cbn in H1. split; [slia | exact (IH (Forall_inv_tail HWsp))]. }
    assert (Hout_const : forall x, aconst_addr x -> outside W x).
    { intros x Hx. clear - HWa Hx. induction W as [|[lo hi] W IH]; cbn; [exact I|].
      pose proof (Forall_inv HWa) as H1. split; [| exact (IH (Forall_inv_tail HWa))].
      intros Hr. apply (H1 x); [cbn; exact Hr | exact Hx]. }
    assert (Hch' : as_chain H (ms_mem ms') (q_s0 Q) (q_CH0 Q)).
    { eapply (chain_via_munch H HH W); [exact r_chain0 | exact HW |]. intros fp ra Hin. apply Hdisj_hi. specialize (r_CH00 fp ra Hin). slia. }
    assert (Hsh0' : sh0_facts (ms_mem ms')).
    { unfold sh0_facts in *. apply Forall_forall. intros [a c] Hac. pose proof (proj1 (Forall_forall _ _) r_sh00 (a, c) Hac) as F0. cbn [fst snd] in *.
      destruct HK_parts as (_ & _ & _ & _ & _ & _ & Hs0). unfold K_sh0_ok in Hs0. rewrite !andb_true_iff in Hs0. destruct Hs0 as [_ Hs0].
      rewrite forallb_forall in Hs0. specialize (Hs0 (a, c) Hac). cbn [fst snd] in Hs0. rewrite !andb_true_iff in Hs0. destruct Hs0 as [[[_ Hlo] Hhi] _].
      apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. unfold sh, ASHADOW_BASE, AIMG_LO, AIMG_TOP in Hlo, Hhi.
      destruct c as [[tv w]| |sl]; [| exact F0 |].
      + destruct F0 as (B0 & B1 & BB). split; [exact B0|]. split; [exact B1|]. intros i Hi. rewrite <- (BB i Hi). unfold mrd. rewrite HW; [reflexivity|].
        rewrite length_Z_to_le_bytes in Hi. rewrite wa_unsigned by slia. apply Hout_const. unfold aconst_addr. do 16 right.
        unfold sh, ASHADOW_BASE, AIMG_LO, AIMG_TOP. slia.
      + cbn [sh0_cell] in F0 |- *. intros j Hj. specialize (F0 j Hj). destruct (sget j sl) as [b|v k|]; [| exact F0 | exact I].
        rewrite <- F0. unfold mrd. rewrite HW; [reflexivity|].
        rewrite wa_unsigned by slia. apply Hout_const. unfold aconst_addr. do 16 right.
        unfold sh, ASHADOW_BASE, AIMG_LO, AIMG_TOP. slia. }
    exists s, LB, G, FF, XS, ms'.
    constructor; cbn [awith_F a_F a_n a_blk a_ff a_cost a_cnt a_cs].
    - exact Hvis'.
    - exact HRn'.
    - exact Hcan'.
    - rewrite Hfr. exact r_fregs0.
    - rewrite Hfc. exact r_fcsr0.
    - rewrite Hrom. exact r_rom0.
    - exact r_rho00.
    - exact r_rho10.
    - exact r_rho20.
    - exact r_rho30.
    - exact r_agree0.
    - exact r_n1.
    - exact Hak'.
    - exact (ah_mpres_trans H HH _ _ _ r_mpres0 Hmp').
    - exact Hheap'.
    - exact Hrfs'.
    - exact Hac'.
    - exact Hst0'.
    - exact Hch'.
    - exact r_CH00.
    - exact r_s0v0.
    - exact r_pfo0.
    - exact r_AL1.
    - exact r_AL00.
    - exact r_G0.
    - (* [comment removed for export] *)
      apply Forall_forall. intros g Hg.
      pose proof (proj1 (Forall_forall _ _) r_Gin0 g Hg) as (Hin & Hrg & Hsz & Htg1 & Htg2 & (rgg & Hgg & Hlog & Hleng & Hkg & Halg & Hdfg) & Hsh).
      split; [exact Hin|]. split; [exact Hrg|]. split; [exact Hsz|]. split; [exact Htg1|]. split; [exact Htg2|]. split.
      + specialize (Hgeom (g_tag g)). rewrite Hgg in Hgeom. destruct (iget (g_tag g) (f_mem F')) as [rg'|]; [|destruct Hgeom].
        destruct Hgeom as (Gl1 & Gl2 & Gl3 & Gl4 & _ & _ & Gl7). exists rg'. split; [reflexivity|]. repeat split; congruence.
      + intros rg' Hrg'.
        (* [comment removed for export] *)
        pose proof (Hgeom (g_tag g + 1)%uint63) as Hgs. rewrite Hrg' in Hgs.
        destruct (iget (g_tag g + 1)%uint63 (f_mem (a_F st))) as [rg1|] eqn:E1; [|destruct Hgs].
        destruct (Hsh rg1 eq_refl) as (-> & Hrs & Had). destruct r_n1 as [_ Hn60]. pose proof (i63_range (g_tag g)).
        rewrite (Hrok (g_tag g + 1)%uint63 _ Hrun ltac:(intros E; apply (f_equal to_Z) in E; rewrite Uint63.add_spec in E; change (to_Z 1%uint63) with 1 in E; change (to_Z 0%uint63) with 0 in E; change wB with (2^63) in E; rewrite Z.mod_small in E by slia; slia) E1 (ro_region_sh _ _)) in Hrg'.
        injection Hrg' as <-. split; [reflexivity|]. split; [exact Hrs|].
        eapply addressable_transport; [exact Had | exact HW | exact Hwm |].
        (* [comment removed for export] *)
        pose proof (ablock_of_G _ _ _ _ _ _ _ _ _ _ _ _ X Hg) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
        pose proof (ah_fsb H HH _ _ _ r_heap0) as (F1 & F2 & F3 & F4).
        assert (BA : 0 <= g_addr g /\ g_addr g + to_Z (g_size g) <= AAPP_HI) by (clear - R1 R2 R3 R4 R5 R6 R7 ACEILB; aapp_unfold; slia).
        pose proof (sh_above_image (g_addr g) ltac:(slia)) as SA.
        unfold W, segW. rewrite !disjoint_from_app. repeat split.
        * apply disjoint_from_map. intros c Hc. cbn [fst snd]. hk_xw c Hc. right. unfold AIMG_TOP in *. slia.
        * right. hk_err. unfold aimg_client_w, ATLS_PRIV_LO, ATLS_PRIV_HI, ALIBC_PGSZ, ATSD0, ATP in *. unfold AIMG_TOP in *. slia.
        * left. pose proof (sh_nsh_high (g_addr g) (to_Z (g_size g)) ltac:(slia) ltac:(slia) (proj2 BA)). unfold AHI_LO in *. slia.
        * apply disjoint_from_map. intros g' Hg'. cbn [fst snd].
          pose proof (ablock_of_G _ _ _ _ _ _ _ _ _ _ _ _ X Hg') as (R1' & R2' & R3' & R4' & R5' & R6' & R7').
          apply (aapp_disjoint_sh _ _ (g_addr g) (to_Z (g_size g)) R7'); slia.
        * apply disjoint_from_map. intros f Hf. cbn [fst snd].
          destruct (aframe_of_FF _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2 & K3 & K4 & K5) _].
          pose proof (fsz_pos (to_Z (f_k f)) ltac:(slia)).
          apply (aapp_disjoint_sh (f_ff f) (AsIface.fsz (to_Z (f_k f))) (g_addr g) (to_Z (g_size g))); [| slia | slia | slia].
          eapply aapp_sub; [exact F4 | unfold AFS_HDR in *; slia | slia].
        * apply disjoint_from_map. intros f Hf. cbn [fst snd].
          destruct (aframe_of_FF _ _ _ _ _ _ _ _ _ _ _ _ X Hf) as [(K1 & K2 & K3 & K4 & K5) _].
          pose proof (frame_al8 _ _ _ (conj K1 (conj K2 (conj K3 (conj K4 K5))))) as A8.
          pose proof (fsz_fshn (to_Z (f_k f)) ltac:(slia)) as [Ef1 Ef2]. pose proof (fsz_pos (to_Z (f_k f)) ltac:(slia)) as FP.
          clear - R2 R3 R6 K2 K3 A8 Ef1 Ef2 FP. unfold AFS_HDR in *. rewrite Ef1. unfold nsh, sh.
          destruct R6 as [R6|R6]; [left | right]; Z.div_mod_to_equations; slia.
    - exact r_Gnodup0.
    - exact r_Gtnd0.
    - exact r_Gnew0.
    - (* [comment removed for export] *) apply Forall_forall. intros g Hg. apply (mrel_stk asegs _ _ _ _ (conj Hwm (conj Hinv' Hrd))).
      exact (proj1 (Forall_forall _ _) r_Gstk0 g Hg).
    - exact r_FF0.
    - (* [comment removed for export] *)
      apply Forall_forall. intros f Hf.
      pose proof (proj1 (Forall_forall _ _) r_FFin0 f Hf) as (Hr0 & Hr1 & Hr2 & Hk & Htg1 & Htg2 & (rgf & Hgf & Hlof & Hlenf & Hkf & Half & Hdff) & (rgs & Hgs & Hlos & Hlens & Hks) & Hflg & X1 & X2 & X3 & X4).
      split; [exact Hr0|]. split; [exact Hr1|]. split; [exact Hr2|]. split; [exact Hk|]. split; [exact Htg1|]. split; [exact Htg2|]. split.
      + specialize (Hgeom (f_tag f)). rewrite Hgf in Hgeom. destruct (iget (f_tag f) (f_mem F')) as [rg'|]; [|destruct Hgeom].
        destruct Hgeom as (Gl1 & Gl2 & Gl3 & Gl4 & _ & _ & Gl7). exists rg'. split; [reflexivity|]. repeat split; congruence.
      + split.
        * specialize (Hgeom (f_tag f + 1)%uint63). rewrite Hgs in Hgeom. destruct (iget (f_tag f + 1)%uint63 (f_mem F')) as [rg'|]; [|destruct Hgeom].
          destruct Hgeom as (Gl1 & Gl2 & Gl3 & Gl4 & _ & _ & Gl7). exists rg'. split; [reflexivity|]. repeat split; congruence.
        * split; [| repeat split; assumption].
          destruct r_n1 as [_ Hn60]. pose proof (i63_range (f_tag f)).
          exact (Hrok (f_tag f + 2)%uint63 _ Hrun ltac:(intros E; apply (f_equal to_Z) in E; rewrite Uint63.add_spec in E; change (to_Z 2%uint63) with 2 in E; change (to_Z 0%uint63) with 0 in E; change wB with (2^63) in E; rewrite Z.mod_small in E by slia; slia) Hflg ro_region_flag).
    - exact r_FFnd0.
    - exact r_FFtnd0.
    - exact r_Tsep0.
    - exact r_FFlen0.
    - exact r_XS0.
    - (* [comment removed for export] *) intros t rg Ht. specialize (Hgeom t). rewrite Ht in Hgeom.
      destruct (iget t (f_mem (a_F st))) as [rg_|] eqn:E; [|destruct Hgeom]. exact (r_dom0 t rg_ E).
    - (* [comment removed for export] *) destruct r_r00 as (rg0 & Hrg0 & Hlo0 & Hlen0 & Hd0 & Hpg0).
      pose proof (Hgeom 0%uint63) as Hg0. rewrite Hrg0 in Hg0. destruct (iget 0%uint63 (f_mem F')) as [rg0'|] eqn:E0'; [|destruct Hg0].
      destruct Hg0 as (Gl1 & Gl2 & _ & Gd1 & _).
      exists rg0'. split; [reflexivity|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
      intros pn p' Hp'. destruct (Hp0 rg0' E0') as (rg0_ & H0_ & Hsub). rewrite Hrg0 in H0_. injection H0_ as <-.
      destruct (Hsub pn p' Hp') as (p & Hp & Hkd). destruct (Hpg0 pn p Hp) as [Hw Hkd']. split; [exact Hw | congruence].
    - (* [comment removed for export] *) destruct r_r10 as (rg1 & Hrg1 & Hlo1 & Hlen1 & Hd1 & Hk1 & Ha1).
      pose proof (Hgeom 1%uint63) as Hg1. rewrite Hrg1 in Hg1. destruct (iget 1%uint63 (f_mem F')) as [rg1'|] eqn:E1; [|destruct Hg1].
      destruct Hg1 as (Gl1 & Gl2 & Gl3 & Gd2 & _ & _ & Gl7). exists rg1'. split; [reflexivity|]. repeat split; congruence.
    - (* [comment removed for export] *) exact (Hrok 2%uint63 _ Hrun ltac:(intros E; discriminate E) r_r20 (ro_region_sh _ _)).
    - (* [comment removed for export] *) exact (Hrok 3%uint63 _ Hrun ltac:(intros E; discriminate E) r_r30 (ro_region_abs _ _ _)).
    - exact Hro'.
    - exact Hinb'.
    - exact Hku'.
    - exact r_cost0.
    - exact r_cnt0.
    - (* [comment removed for export] *) exact (mrel_stk asegs _ _ _ _ (conj Hwm (conj Hinv' Hrd)) r_stk0).
    - exact r_lo0.
    - exact Haux'.
    - exact (Hinv' r_inv0).
    - exact (mrel_stk asegs _ _ _ _ (conj Hwm (conj Hinv' Hrd)) r_err0).
    - exact Hsh0'.
    - exact r_LB1.
    - exact r_LB0h0.
    - exact r_named1.
    - exact r_LBsub0.
    - (* [comment removed for export] *) intros a Ha Hcl Hna Hnx Hne Hnxs. rewrite <- (r_frame0 a Ha Hcl Hna Hnx Hne Hnxs).
      destruct (rb_addr_dec a) as [(b & Hb & Eb) | Hnrb].
      { apply Hrof. exists b, tt. split; [exact (ro_of_rb b Hb)|]. rewrite Eb. reflexivity. }
      apply HW. rewrite wa_unsigned by slia. unfold W, segW. rewrite !outside_app. repeat split.
      + apply outside_map. intros c Hc. cbn [fst snd]. intros Hin. apply Hnx. split; [exists c; split; [exact Hc | slia] | exact Hnrb].
      + cbn [fst snd]. intros Hin. apply Hne. split; [exact Hin | exact Hnrb].
      + cbn [fst snd]. pose proof (ah_fsb H HH _ _ _ r_heap0) as (F1 & F2 & F3 & F4).
        unfold client0, aclient_addr in Hcl.
        destruct Hcl as [Hsp | [Hst | [(b & Hb & Hr) | [(b & Hb & Hr) | [Hfs | [Hfss | Hss]]]]]].
        * slia.
        * unfold aimg_client in Hst. slia.
        * pose proof (r_LB0h0 b Hb). slia.
        * pose proof (r_LB0h0 b Hb) as [B0 B1].
          intros [K1 K2]. clear - Hr B0 B1 ACEILB Hal Hl2 K1 Hcs. unfold nsh, sh, ASHADOW_BASE in *. Z.div_mod_to_equations. slia.
        * slia.
        * pose proof (sh_below_aceil (as_FSB H + AFS_SIZE) ltac:(aapp_unfold; unfold AFS_SIZE in *; slia)). slia.
        * unfold AHI_LO in Hss. slia.
      + apply outside_map. intros g Hg. cbn [fst snd].
        destruct (proj1 (Forall_forall _ _) r_Gnew0 g Hg) as [Hn | [Hd _]].
        * intros Hr. apply Hna. exists g. split; [exact Hn | left; exact Hr].
        * exact (proj1 (Hd a Hcl Hna)).
      + apply outside_map. intros f Hf. cbn [fst snd]. intros Hr. apply Hnxs.
        pose proof (proj1 (Forall_forall _ _) r_FFin0 f Hf) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X2 & _ & _). exact (X2 a Hr).
      + apply outside_map. intros f Hf. cbn [fst snd]. intros Hr. apply Hnxs.
        pose proof (proj1 (Forall_forall _ _) r_FFin0 f Hf) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X3 & _). exact (X3 a Hr).
    - (* [comment removed for export] *) apply Forall_forall. intros f Hf. apply (mrel_stk asegs _ _ _ _ (conj Hwm (conj Hinv' Hrd))).
      exact (proj1 (Forall_forall _ _) r_FFstk0 f Hf).
  Qed.
End Inv.
