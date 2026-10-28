(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_free Fz_M_secure
     Fz_W1_defs Fz_W1_sync Fz_W3_iface.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).

Definition J_END : Z := 0x1881e0.
Definition J_OUTFREE : Z := 0x1887dc.
(* [comment removed for export] *)
Definition pem_loc (l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 ta tb : word) : list cell := [C8 l0; C8 l1; C8 l2; C8 l3; C8 l4; C8 l5; C8 l6; C8 l7; C8 l8; C8 l9; C8 l10; C8 l11; C4 ta; C4 tb].

(* [comment removed for export] *)
Definition bio_free_null_stmt `{CE__ : Ceiling} `{RN__ : RunRnd} : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB0 : list block) (L : @clist bptr) (f : nat) (lo B : Z),
  cstate s LBall LB0 L m sp tp lo B -> lo <= bv_unsigned sp - 64 -> a0 = wz 0 ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_BIO_FREE) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB0 L f m lo B (fun _ => False) [] 0 0 0 0 (fun v LBall' L' _ => v = wz 0 /\ LBall' = LBall /\ L' = L)).

(* [comment removed for export] *)
Record pem_entry : Type := PEMENT {
  e_ra : word; e_sp : word; e_gp : word; e_tp : word; e_s0 : word; e_s1 : word; e_s2 : word; e_s3 : word; e_s4 : word; e_s5 : word; e_s6 : word; e_s7 : word;
  e_s8 : word; e_s9 : word; e_s10 : word; e_s11 : word; e_F : bvmap 5 word; e_fc : bv 32;
  e_s : PState; e_LBall : list block; e_LB0 : list block; e_LBL : list block; e_L : @clist bptr; e_f : nat; e_m : mem; e_lo : Z; e_B : Z;
  e_K : mbk; e_pe : bptr; e_BI : Z; e_meth : Z; e_blen : Z; e_bmax : Z; e_boff : Z; e_flags : Z; e_E : Z; e_Enm : Z }.
Definition e_PL (en : pem_entry) : Z := bv_unsigned (e_sp en).
Definition pem_EV (en : pem_entry) : nat := Z.to_nat (40 + 2 * (e_blen en - e_boff en)).
Definition pem_BIG (en : pem_entry) : Z := 6 * (e_blen en - e_boff en) + 4 * (256 + 8192) + 65536.
Definition pem_T (en : pem_entry) : bptr -> Prop := fun q => mbio_T (e_K en) q \/ q = e_pe en.
(* [comment removed for export] *)
Definition pem_saved (en : pem_entry) : list cell :=
  [C8 (e_s11 en); C8 (e_s10 en); C8 (e_s9 en); C8 (e_s8 en); C8 (e_s7 en); C8 (e_s6 en); C8 (e_s5 en); C8 (e_s4 en); C8 (e_s3 en); C8 (e_s2 en); C8 (e_s1 en);
   C8 (e_s0 en); C8 (e_ra en)].

Section W3. Context {CE__ : Ceiling} {RN__ : RunRnd}.
  Variable libenv : mem -> list block -> Z -> Prop.
  Variable errst_at_rest : Z -> list block -> mem -> Prop.
  Variable errst_live : Z -> Z -> Z -> list block -> mem -> Prop.

  Definition pem_post (en : pem_entry) : nat -> @clist bptr -> PState -> machine_state -> Prop :=
    cpostx (e_ra en) (e_sp en) (e_gp en) (e_tp en) (e_s0 en) (e_s1 en) (e_s2 en) (e_s3 en) (e_s4 en) (e_s5 en) (e_s6 en) (e_s7 en) (e_s8 en) (e_s9 en) (e_s10 en) (e_s11 en)
           (e_F en) (e_fc en) (e_s en) (e_LBall en) (e_LB0 en) (e_L en) (e_f en) (e_m en) (e_lo en) (e_B en) (pem_T en) [] (e_PL en + 32)
           (pem_EV en) 16 8 (pem_BIG en) (pem_read_res libenv errst_live (e_K en) (e_BI en) (e_meth en) (e_blen en) (e_bmax en) (e_boff en) (e_PL en) (e_E en) (e_LBL en) (e_LBall en) (e_L en)).

  (* [comment removed for export] *)
  Definition pem_com (en : pem_entry) (s : PState) (LBc : list block) (Lc : @clist bptr) (f : nat) (m : mem) (off : Z) (rem : nat) (rA rB rBig : Z) : Prop :=
       cstate s LBc (e_LB0 en) Lc m (wz (e_PL en + -208)) (e_tp en) (e_lo en) (e_B en)
    /\ cframe (pem_T en) [] (e_PL en + 32) (e_s en) (e_LBall en) (e_L en) (e_m en) s LBc Lc m
    /\ libenv m (e_LBL en) (e_E en) /\ incl_blocks (e_LBL en) (e_LBall en) /\ incl_blocks (e_LBL en) LBc /\ (forall b, In b (e_LBL en) -> ~ pem_T en (blk_id b))
    /\ cown LBc Lc (e_pe en) (e_E en) 904 (e_Enm en)
    /\ mbio_rep m LBc Lc (e_K en) (e_BI en) (e_meth en) (e_blen en) (e_bmax en) off /\ e_boff en <= off <= e_blen en
    /\ (pem_EV en <= e_f en)%nat /\ (e_f en - pem_EV en + rem <= f)%nat
    /\ croom Lc rA rB rBig /\ cgrow (e_L en) Lc (16 - rA) (8 - rB) (pem_BIG en - rBig) /\ 0 <= rA /\ 0 <= rB /\ 0 <= rBig
    /\ incl_blocks (e_LBall en) LBc /\ (forall q nm, In (q, nm) (e_L en) -> In (q, nm) Lc)
    /\ rw_cells usegs m (e_PL en + -104) (pem_saved en)
    /\ e_lo en <= e_PL en + -208 - BPUTS_STACK /\ e_PL en + 32 <= e_B en /\ 0 <= e_flags en < 256 /\ e_PL en mod 16 = 0
    /\ In (e_pe en) (map blk_id (e_LBall en)) /\ (forall q, mbio_T (e_K en) q -> In q (map blk_id (e_LBall en))).

  (* [comment removed for export] *)
  Definition pem_err (en : pem_entry) (strs : list block) (m : mem) : Prop :=
    (strs = [] /\ errst_at_rest (e_E en) [] m) \/ (exists top bot, errst_live (e_E en) top bot strs m /\ (length strs <= 2)%nat).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition END0_stmt : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig strs loc
           (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s10 s11 t3 t4 t5 t6 : word),
    pem_com en s LBc Lc f m off rem rA rB rBig -> pem_err en strs m ->
    (forall b, In b LBc -> In b (e_LBall en) \/ In b strs) -> incl_blocks strs LBc -> strs_inL Lc strs -> (forall b, In b strs -> ~ In (blk_id b) (map blk_id (e_LBall en))) ->
    List.NoDup (map blk_id strs) ->
    rw_cells usegs m (e_PL en + -208) loc -> Z.of_nat (cells_size loc) = 104 ->
    rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) (wz 0) a0 a1 a2 a3 a4 a5 a6 a7
                       (wz 0) (wz 0) s4 (wz (e_flags en)) (wz 0) s7 (wz (e_PL en + 24)) (wz 0) s10 s11 t3 t4 t5 t6) (e_F en) (wz J_END) (e_fc en) None m (seg_rom usegs))
      (pem_post en).

  (* [comment removed for export] *)
  Definition opt_ids (o : option bptr) : list bptr := match o with Some q => [q] | None => [] end.
  Definition END_stmt : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig loc strs news
           (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s10 s11 t3 t4 t5 t6 : word)
           (octx oname : option bptr) (ctxv namev nn hBv dBv ret : Z)
           (KX KY : mbk) (BMX BMY methX methY lenX maxX offX lenY maxY offY : Z) (blwX blwY : word),
    let curids := mbio_blocks KX ++ mbio_blocks KY ++ opt_ids octx ++ opt_ids oname in
    pem_com en s LBc Lc f m off rem rA rB rBig -> pem_err en strs m -> (12 <= rem)%nat ->
    rw_cells usegs m (e_PL en + -208) loc -> Z.of_nat (cells_size loc) = 104 ->
    match octx with None => ctxv = 0 | Some qc => cown LBc Lc qc ctxv ECTX ECTX end ->
    match oname with None => namev = 0 | Some qn => cown LBc Lc qn namev nn nn /\ 1 <= nn /\ rw_cells usegs m namev [CB 0%nat []] end ->
    mbio_repx m LBc Lc KX hBv BMX blwX methX lenX maxX offX -> mbio_repx m LBc Lc KY dBv BMY blwY methY lenY maxY offY ->
    (* [comment removed for export] *)
    (forall b, In b LBc -> In b (e_LBall en) \/ In (blk_id b) curids \/ In b (strs ++ news)) -> incl_blocks (strs ++ news) LBc -> strs_inL Lc strs ->
    (forall b, In b (e_LBall en) -> ~ In (blk_id b) curids) -> (forall b, In b (strs ++ news) -> ~ In (blk_id b) (map blk_id (e_LBall en))) ->
    (forall q nm, In (q, nm) (e_L en) -> ~ In q curids) ->
    List.NoDup (curids ++ map blk_id (strs ++ news) ++ e_pe en :: mbio_blocks (e_K en)) ->
    pem_out ret m LBc Lc (e_PL en + 24) (e_PL en + 16) (e_PL en + 8) (e_PL en) news -> news_sz news <= 2 * (off - e_boff en) + 256 ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) (wz dBv) a0 a1 a2 a3 a4 a5 a6 a7
                       (wz namev) (wz ret) s4 (wz (e_flags en)) (wz hBv) s7 (wz (e_PL en + 24)) (wz ctxv) s10 s11 t3 t4 t5 t6) (e_F en) (wz J_END) (e_fc en) None m (seg_rom usegs))
      (pem_post en).

  (* [comment removed for export] *)
  Definition OUTFREE_stmt : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig strs
           (xra t0 t1 t2 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s7 s11 t3 t4 t5 t6 l0 l1 l3 l4 l5 l8 l9 l11 ta tb : word)
           (qc qn qh : bptr) (ctxv namev nn HD nh hBv dBv : Z) (bh : list byte)
           (KX KY : mbk) (BMX BMY methX methY lenX maxX offX lenY maxY offY : Z) (blwX blwY : word),
    let curids := mbio_blocks KX ++ mbio_blocks KY ++ [qc; qn; qh] in
    pem_com en s LBc Lc f m off rem rA rB rBig -> pem_err en strs m -> (14 <= rem)%nat ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 l1 (wz namev) l3 l4 l5 (wz (e_PL en + 8)) (wz (e_PL en + 16)) l8 l9 (wz (e_flags en)) l11 ta tb) ->
    cown LBc Lc qc ctxv ECTX ECTX -> cown LBc Lc qn namev nn nn -> 1 <= nn ->
    cown LBc Lc qh HD nh nh -> 1 <= nh -> length bh = Z.to_nat nh -> rw_cells usegs m HD [CB (Z.to_nat nh) bh] ->
    mbio_repx m LBc Lc KX hBv BMX blwX methX lenX maxX offX -> mbio_repx m LBc Lc KY dBv BMY blwY methY lenY maxY offY ->
    (forall b, In b LBc -> In b (e_LBall en) \/ In (blk_id b) curids \/ In b strs) -> incl_blocks strs LBc -> strs_inL Lc strs ->
    (forall b, In b (e_LBall en) -> ~ In (blk_id b) curids) -> (forall b, In b strs -> ~ In (blk_id b) (map blk_id (e_LBall en))) ->
    (forall q nm, In (q, nm) (e_L en) -> ~ In q curids) ->
    List.NoDup (curids ++ map blk_id strs ++ e_pe en :: mbio_blocks (e_K en)) ->
    rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz HD); C8 (wz 0)] ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) s1 a0 (wz HD) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 (wz (e_flags en)) (wz hBv) s7 (wz (e_PL en + 24)) (wz ctxv) (wz dBv) s11 t3 t4 t5 t6) (e_F en) (wz J_OUTFREE) (e_fc en) None m (seg_rom usegs))
      (pem_post en).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition J_TAIL : Z := 0x188508.   (* [comment removed for export] *)
  Definition J_INI : Z := 0x1885d0.    (* [comment removed for export] *)
  Definition J_DEC : Z := 0x188688.    (* [comment removed for export] *)
  Definition J_RZT : Z := 0x188764.    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition TAIL_stmt : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig
           (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s9 s10 s11 t3 t4 t5 t6 l0 l1 l3 l4 l5 l8 l9 l11 ta tb : word)
           (qn : bptr) (namev nn hBv dBv : Z) (bn : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    let curids := mbio_blocks KX ++ mbio_blocks KY ++ [qn] in
    pem_com en s LBc Lc f m off rem rA rB rBig -> errst_at_rest (e_E en) [] m -> (17 <= rem)%nat -> 3 <= rA -> 2 <= rB -> wBig (lenX + 1) + wBig lenY <= rBig -> lenX + lenY <= 2 * (off - e_boff en) ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 l1 (wz namev) l3 l4 l5 (wz (e_PL en + 8)) (wz (e_PL en + 16)) l8 l9 (wz (e_flags en)) l11 ta tb) ->
    cown LBc Lc qn namev nn nn -> 1 <= nn <= 255 -> length bn = Z.to_nat nn -> rw_cells usegs m namev [CB (Z.to_nat nn) bn] -> In (Z_to_bv 8 0) bn ->
    mbio_rep m LBc Lc KX hBv methX lenX maxX 0 -> mbio_rep m LBc Lc KY dBv methY lenY maxY 0 ->
    (forall b, In b LBc -> In b (e_LBall en) \/ In (blk_id b) curids) ->
    (forall b, In b (e_LBall en) -> ~ In (blk_id b) curids) -> (forall q nm, In (q, nm) (e_L en) -> ~ In q curids) ->
    List.NoDup (curids ++ e_pe en :: mbio_blocks (e_K en)) ->
    rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) (wz dBv) a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 (wz (e_flags en)) (wz hBv) (e_sp en) (wz (e_PL en + 24)) s9 s10 s11 t3 t4 t5 t6) (e_F en) (wz J_TAIL) (e_fc en) None m (seg_rom usegs))
      (pem_post en).

  (* [comment removed for export] *)
  Definition INI_stmt : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig
           (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s9 s10 s11 t3 t4 t5 t6 l0 l1 l3 l4 l5 l8 l9 ta : word)
           (qc qn : bptr) (ctxv namev nn hBv dBv BMY : Z) (bn : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    let curids := mbio_blocks KX ++ mbio_blocks KY ++ [qc; qn] in
    pem_com en s LBc Lc f m off rem rA rB rBig -> errst_at_rest (e_E en) [] m -> (16 <= rem)%nat -> 2 <= rA -> 2 <= rB -> wBig (lenX + 1) + wBig lenY <= rBig -> lenX + lenY <= 2 * (off - e_boff en) ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 l1 (wz namev) l3 l4 l5 (wz (e_PL en + 8)) (wz (e_PL en + 16)) l8 l9 (wz (e_flags en)) (wz BMY) ta (wz lenY)) ->
    cown LBc Lc qc ctxv ECTX ECTX -> rw_cells usegs m ctxv [CB (Z.to_nat ECTX) (repeat (Z_to_bv 8 0) (Z.to_nat ECTX))] ->
    cown LBc Lc qn namev nn nn -> 1 <= nn <= 255 -> length bn = Z.to_nat nn -> rw_cells usegs m namev [CB (Z.to_nat nn) bn] -> In (Z_to_bv 8 0) bn ->
    mbio_rep m LBc Lc KX hBv methX lenX maxX 0 -> mbio_repx m LBc Lc KY dBv BMY (wz lenY) methY lenY maxY 0 -> 1 <= lenY ->
    (forall b, In b LBc -> In b (e_LBall en) \/ In (blk_id b) curids) ->
    (forall b, In b (e_LBall en) -> ~ In (blk_id b) curids) -> (forall q nm, In (q, nm) (e_L en) -> ~ In q curids) ->
    List.NoDup (curids ++ e_pe en :: mbio_blocks (e_K en)) ->
    rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) (wz dBv) (wz ctxv) a1 a2 a3 a4 a5 a6 a7
                       (wz lenY) s3 s4 (wz (e_flags en)) (wz hBv) (e_sp en) (wz (e_PL en + 24)) s9 s10 s11 t3 t4 t5 t6) (e_F en) (wz J_INI) (e_fc en) None m (seg_rom usegs))
      (pem_post en).

  (* [comment removed for export] *)
  Definition RZT_stmt : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig
           (xra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s7 s11 t3 t4 t5 t6 l0 l1 l3 l4 l5 l6 l7 l8 l9 l11 ta tb : word)
           (qc qn : bptr) (ctxv namev nn hBv dBv : Z) (bn : list byte)
           (KX KY : mbk) (BMX BMY methX methY lenX maxX offX lenY maxY offY : Z) (blwX blwY : word),
    let curids := mbio_blocks KX ++ mbio_blocks KY ++ [qc; qn] in
    pem_com en s LBc Lc f m off rem rA rB rBig -> errst_at_rest (e_E en) [] m -> (14 <= rem)%nat -> 2 <= rA ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 l1 (wz namev) l3 l4 l5 l6 l7 l8 l9 (wz (e_flags en)) l11 ta tb) ->
    cown LBc Lc qc ctxv ECTX ECTX ->
    cown LBc Lc qn namev nn nn -> 1 <= nn <= 255 -> length bn = Z.to_nat nn -> rw_cells usegs m namev [CB (Z.to_nat nn) bn] -> In (Z_to_bv 8 0) bn ->
    mbio_repx m LBc Lc KX hBv BMX blwX methX lenX maxX offX -> mbio_repx m LBc Lc KY dBv BMY blwY methY lenY maxY offY ->
    (forall b, In b LBc -> In b (e_LBall en) \/ In (blk_id b) curids) ->
    (forall b, In b (e_LBall en) -> ~ In (blk_id b) curids) -> (forall q nm, In (q, nm) (e_L en) -> ~ In q curids) ->
    List.NoDup (curids ++ e_pe en :: mbio_blocks (e_K en)) ->
    rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 (wz (e_flags en)) (wz hBv) s7 (wz (e_PL en + 24)) (wz ctxv) (wz dBv) s11 t3 t4 t5 t6) (e_F en) (wz J_RZT) (e_fc en) None m (seg_rom usegs))
      (pem_post en).

  (* [comment removed for export] *)
  Definition DEC_stmt : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig
           (xra t0 t1 t2 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s11 t3 t4 t5 t6 l0 l1 l3 l4 l5 l8 l9 l11 ta : word)
           (qc qn : bptr) (ctxv namev nn hBv dBv BMY dlen : Z) (bn : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    let curids := mbio_blocks KX ++ mbio_blocks KY ++ [qc; qn] in
    pem_com en s LBc Lc f m off rem rA rB rBig -> errst_at_rest (e_E en) [] m -> (16 <= rem)%nat -> 2 <= rA -> 2 <= rB -> wBig (lenX + 1) + wBig lenY <= rBig -> lenX + lenY <= 2 * (off - e_boff en) ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 l1 (wz namev) l3 l4 l5 (wz (e_PL en + 8)) (wz (e_PL en + 16)) l8 l9 (wz (e_flags en)) l11 ta (wz dlen)) ->
    cown LBc Lc qc ctxv ECTX ECTX ->
    cown LBc Lc qn namev nn nn -> 1 <= nn <= 255 -> length bn = Z.to_nat nn -> rw_cells usegs m namev [CB (Z.to_nat nn) bn] -> In (Z_to_bv 8 0) bn ->
    mbio_rep m LBc Lc KX hBv methX lenX maxX 0 -> mbio_repx m LBc Lc KY dBv BMY (wz dlen) methY lenY maxY 0 -> 0 <= dlen <= lenY ->
    (forall b, In b LBc -> In b (e_LBall en) \/ In (blk_id b) curids) ->
    (forall b, In b (e_LBall en) -> ~ In (blk_id b) curids) -> (forall q nm, In (q, nm) (e_L en) -> ~ In q curids) ->
    List.NoDup (curids ++ e_pe en :: mbio_blocks (e_K en)) ->
    rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) s1 (wz hBv) a1 (wz 0) a3 a4 a5 a6 a7
                       s2 s3 s4 (wz (e_flags en)) (wz hBv) (e_sp en) (wz (e_PL en + 24)) (wz ctxv) (wz dBv) s11 t3 t4 t5 t6) (e_F en) (wz J_DEC) (e_fc en) None m (seg_rom usegs))
      (pem_post en).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition J_RAISE2 : Z := 0x188570.  (* [comment removed for export] *)
  Definition J_FREE2 : Z := 0x18859c.   (* [comment removed for export] *)

  Definition FREE2_stmt : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig strs
           (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s7 s9 s11 t3 t4 t5 t6 l0 l1 l3 l4 l6 l7 l8 l10 l11 ta tb : word)
           (qn ql : bptr) (namev nn LB2 hBv dBv : Z) (bn bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    let curids := mbio_blocks KX ++ mbio_blocks KY ++ [qn; ql] in
    pem_com en s LBc Lc f m off rem rA rB rBig -> pem_err en strs m -> (13 <= rem)%nat ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 l1 (wz namev) l3 l4 (wz LB2) l6 l7 l8 (wz dBv) l10 l11 ta tb) ->
    cown LBc Lc qn namev nn nn -> 1 <= nn <= 255 -> length bn = Z.to_nat nn -> rw_cells usegs m namev [CB (Z.to_nat nn) bn] -> In (Z_to_bv 8 0) bn ->
    cown LBc Lc ql LB2 256 256 -> length bs = 256%nat -> rw_cells usegs m LB2 [CB 256 bs] ->
    mbio_rep m LBc Lc KX hBv methX lenX maxX 0 -> mbio_rep m LBc Lc KY dBv methY lenY maxY 0 ->
    (forall b, In b LBc -> In b (e_LBall en) \/ In (blk_id b) curids \/ In b strs) -> incl_blocks strs LBc -> strs_inL Lc strs ->
    (forall b, In b (e_LBall en) -> ~ In (blk_id b) curids) -> (forall b, In b strs -> ~ In (blk_id b) (map blk_id (e_LBall en))) ->
    (forall q nm, In (q, nm) (e_L en) -> ~ In q curids) ->
    List.NoDup (curids ++ map blk_id strs ++ e_pe en :: mbio_blocks (e_K en)) ->
    rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) (wz dBv) a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 (wz (e_flags en)) (wz hBv) s7 (wz (e_PL en + 24)) s9 (wz LB2) s11 t3 t4 t5 t6) (e_F en) (wz J_FREE2) (e_fc en) None m (seg_rom usegs))
      (pem_post en).

  Definition RAISE2_stmt : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig
           (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s7 s9 t3 t4 t5 t6 l0 l1 l3 l4 l6 l7 l8 l10 l11 ta tb : word)
           (qn ql : bptr) (namev nn LB2 hBv dBv line : Z) (bn bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    let curids := mbio_blocks KX ++ mbio_blocks KY ++ [qn; ql] in
    pem_com en s LBc Lc f m off rem rA rB rBig -> errst_at_rest (e_E en) [] m -> (15 <= rem)%nat -> 2 <= rA -> 0 <= line < 2 ^ 31 ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 l1 (wz namev) l3 l4 (wz LB2) l6 l7 l8 (wz dBv) l10 l11 ta tb) ->
    cown LBc Lc qn namev nn nn -> 1 <= nn <= 255 -> length bn = Z.to_nat nn -> rw_cells usegs m namev [CB (Z.to_nat nn) bn] -> In (Z_to_bv 8 0) bn ->
    cown LBc Lc ql LB2 256 256 -> length bs = 256%nat -> rw_cells usegs m LB2 [CB 256 bs] ->
    mbio_rep m LBc Lc KX hBv methX lenX maxX 0 -> mbio_rep m LBc Lc KY dBv methY lenY maxY 0 ->
    (forall b, In b LBc -> In b (e_LBall en) \/ In (blk_id b) curids) ->
    (forall b, In b (e_LBall en) -> ~ In (blk_id b) curids) -> (forall q nm, In (q, nm) (e_L en) -> ~ In q curids) ->
    List.NoDup (curids ++ e_pe en :: mbio_blocks (e_K en)) ->
    rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) (wz dBv) a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 (wz (e_flags en)) (wz hBv) s7 (wz (e_PL en + 24)) s9 (wz LB2) (wz line) t3 t4 t5 t6) (e_F en) (wz J_RAISE2) (e_fc en) None m (seg_rom usegs))
      (pem_post en).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition J_ENDLINE : Z := 0x18847c.
  Definition J_LFREE : Z := 0x1884f4.

  Definition LFREE_stmt : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig
           (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s9 s11 t3 t4 t5 t6 l0 l1 l3 l4 l8 l9 l11 ta tb : word)
           (qn ql : bptr) (namev nn LB2 hBv dBv : Z) (bn bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    let curids := mbio_blocks KX ++ mbio_blocks KY ++ [qn; ql] in
    pem_com en s LBc Lc f m off rem rA rB rBig -> errst_at_rest (e_E en) [] m -> (18 <= rem)%nat -> 3 <= rA -> 2 <= rB -> wBig (lenX + 1) + wBig lenY <= rBig -> lenX + lenY <= 2 * (off - e_boff en) ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 l1 (wz namev) l3 l4 (wz LB2) (wz (e_PL en + 8)) (wz (e_PL en + 16)) l8 l9 (wz (e_flags en)) l11 ta tb) ->
    cown LBc Lc qn namev nn nn -> 1 <= nn <= 255 -> length bn = Z.to_nat nn -> rw_cells usegs m namev [CB (Z.to_nat nn) bn] -> In (Z_to_bv 8 0) bn ->
    cown LBc Lc ql LB2 256 256 -> length bs = 256%nat -> rw_cells usegs m LB2 [CB 256 bs] ->
    mbio_rep m LBc Lc KX hBv methX lenX maxX 0 -> mbio_rep m LBc Lc KY dBv methY lenY maxY 0 ->
    (forall b, In b LBc -> In b (e_LBall en) \/ In (blk_id b) curids) ->
    (forall b, In b (e_LBall en) -> ~ In (blk_id b) curids) -> (forall q nm, In (q, nm) (e_L en) -> ~ In q curids) ->
    List.NoDup (curids ++ e_pe en :: mbio_blocks (e_K en)) ->
    rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) (wz dBv) a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 (wz (e_flags en)) (wz hBv) (e_sp en) (wz (e_PL en + 24)) s9 (wz LB2) s11 t3 t4 t5 t6) (e_F en) (wz J_LFREE) (e_fc en) None m (seg_rom usegs))
      (pem_post en).

  Definition ENDLINE_stmt : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig
           (xra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s11 t3 t4 t5 t6 l0 l1 l3 l4 l8 l11 ta tb : word)
           (qn ql : bptr) (namev nn LB2 hBv dBv got : Z) (str bn2 bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    let curids := mbio_blocks KX ++ mbio_blocks KY ++ [qn; ql] in
    pem_com en s LBc Lc f m off rem rA rB rBig -> errst_at_rest (e_E en) [] m -> (18 <= rem)%nat -> 3 <= rA -> 2 <= rB ->
    wBig (lenX + 1) + wBig (lenY + 1) <= rBig -> lenX + lenY <= 2 * (off - e_boff en) ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 l1 (wz namev) l3 l4 (wz LB2) (wz (e_PL en + 8)) (wz (e_PL en + 16)) l8 (wz dBv) (wz (e_flags en)) l11 ta tb) ->
    0 <= got <= 2 -> (got = 0 -> l1 = wz hBv) ->
    cown LBc Lc qn namev nn nn -> 1 <= nn <= 239 -> length (str ++ Z_to_bv 8 0 :: bn2) = Z.to_nat nn ->
    rw_cells usegs m namev [CB (Z.to_nat nn) (str ++ Z_to_bv 8 0 :: bn2)] -> ~ In (Z_to_bv 8 0) str ->
    cown LBc Lc ql LB2 256 256 -> length bs = 256%nat -> rw_cells usegs m LB2 [CB 256 bs] ->
    mbio_rep m LBc Lc KX hBv methX lenX maxX 0 -> mbio_rep m LBc Lc KY dBv methY lenY maxY 0 ->
    (forall b, In b LBc -> In b (e_LBall en) \/ In (blk_id b) curids) ->
    (forall b, In b (e_LBall en) -> ~ In (blk_id b) curids) -> (forall q nm, In (q, nm) (e_L en) -> ~ In q curids) ->
    List.NoDup (curids ++ e_pe en :: mbio_blocks (e_K en)) ->
    rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 (wz got) s4 (wz (e_flags en)) (wz hBv) (e_sp en) (wz (e_PL en + 24)) (wz (e_BI en)) (wz LB2) s11 t3 t4 t5 t6) (e_F en) (wz J_ENDLINE) (e_fc en) None m (seg_rom usegs))
      (pem_post en).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition owA (K : mbk) (mx : Z) : Z := match k_d K with Some _ => wA mx | None => 0 end.
  Definition owB (K : mbk) (mx : Z) : Z := match k_d K with Some _ => wB mx | None => 0 end.
  Definition owBig (K : mbk) (mx : Z) : Z := match k_d K with Some _ => wBig mx | None => 0 end.
  Definition J_HD : Z := 0x188308.
  Definition J_HD2 : Z := 0x188378.
  Definition PEM_ENDSTR : Z := 0x255f0.

  (* [comment removed for export] *)
  Definition hd_core (en : pem_entry) (LBc : list block) (Lc : @clist bptr) (m : mem) (rA rB rBig : Z)
      (qn ql : bptr) (namev nn LB2 hBv dBv tmpv ov got : Z) (str bn2 bs : list byte) (KT KO : mbk) (methT methO lenT maxT lenO maxO : Z) : Prop :=
    let curids := mbio_blocks KT ++ mbio_blocks KO ++ [qn; ql] in
       errst_at_rest (e_E en) [] m /\ (0 <= e_boff en /\ e_blen en < 2 ^ 26)
    /\ 5 <= rA + owA KT maxT + owA KO maxO /\ 4 <= rB + owB KT maxT + owB KO maxO
    /\ 6 * (e_blen en - e_boff en) + 32778 <= rBig + owBig KT maxT + owBig KO maxO
    /\ 3 * maxT <= 4 * lenT + 12 /\ 3 * maxO <= 4 * lenO + 12
    /\ (forall d, k_d KT = Some d -> In (d, maxT) Lc) /\ (forall d, k_d KO = Some d -> In (d, maxO) Lc)
    /\ 0 <= got <= 2 /\ ((got <> 2 /\ tmpv = hBv /\ ov = dBv) \/ (got = 2 /\ tmpv = dBv /\ ov = hBv))
    /\ cown LBc Lc qn namev nn nn /\ 1 <= nn <= 239 /\ length (str ++ Z_to_bv 8 0 :: bn2) = Z.to_nat nn
    /\ rw_cells usegs m namev [CB (Z.to_nat nn) (str ++ Z_to_bv 8 0 :: bn2)] /\ ~ In (Z_to_bv 8 0) str
    /\ cown LBc Lc ql LB2 256 256 /\ length bs = 256%nat /\ rw_cells usegs m LB2 [CB 256 bs]
    /\ mbio_rep m LBc Lc KT tmpv methT lenT maxT 0 /\ mbio_rep m LBc Lc KO ov methO lenO maxO 0
    /\ (forall b, In b LBc -> In b (e_LBall en) \/ In (blk_id b) curids)
    /\ (forall b, In b (e_LBall en) -> ~ In (blk_id b) curids) /\ (forall q nm, In (q, nm) (e_L en) -> ~ In q curids)
    /\ List.NoDup (curids ++ e_pe en :: mbio_blocks (e_K en))
    /\ rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
  (* [comment removed for export] *)
  Definition hd_inv (en : pem_entry) (LBc : list block) (Lc : @clist bptr) (m : mem) (off : Z) (rem : nat) (rA rB rBig : Z)
      (qn ql : bptr) (namev nn LB2 hBv dBv tmpv ov got len : Z) (str bn2 bs : list byte) (KT KO : mbk) (methT methO lenT maxT lenO maxO : Z) : Prop :=
       hd_core en LBc Lc m rA rB rBig qn ql namev nn LB2 hBv dBv tmpv ov got str bn2 bs KT KO methT methO lenT maxT lenO maxO
    /\ (Z.to_nat (2 * (e_blen en - off) + 18) <= rem)%nat /\ lenT + lenO <= 2 * (off - e_boff en - len)
    /\ 1 <= len <= 254 /\ nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0).
  (* [comment removed for export] *)
  Definition gets_pre (en : pem_entry) (LBc : list block) (Lc : @clist bptr) (m : mem) (off : Z) (rem : nat) (rA rB rBig : Z)
      (qn ql : bptr) (namev nn LB2 hBv dBv tmpv ov got : Z) (str bn2 bs : list byte) (KT KO : mbk) (methT methO lenT maxT lenO maxO : Z) : Prop :=
       hd_core en LBc Lc m rA rB rBig qn ql namev nn LB2 hBv dBv tmpv ov got str bn2 bs KT KO methT methO lenT maxT lenO maxO
    /\ (Z.to_nat (2 * (e_blen en - off) + 16) <= rem)%nat /\ lenT + lenO <= 2 * (off - e_boff en).

  Definition HD_at (N : Z) : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig
           (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 l0 l3 l8 l11 ta tb : word)
           (qn ql : bptr) (namev nn LB2 hBv dBv tmpv ov got prev endv len : Z) (str bn2 bs : list byte) (KT KO : mbk) (methT methO lenT maxT lenO maxO : Z),
    e_blen en - off <= N ->
    pem_com en s LBc Lc f m off rem rA rB rBig ->
    hd_inv en LBc Lc m off rem rA rB rBig qn ql namev nn LB2 hBv dBv tmpv ov got len str bn2 bs KT KO methT methO lenT maxT lenO maxO ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 (wz tmpv) (wz namev) l3 (wz endv) (wz LB2) (wz (e_PL en + 8)) (wz (e_PL en + 16)) l8 (wz dBv) (wz (e_flags en)) l11 ta tb) ->
    (endv = 0 \/ endv = 1) -> (prev = 0 \/ prev = 1) ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) (wz prev) a0 a1 a2 a3 a4 a5 a6 a7
                       (wz PEM_ENDSTR) (wz got) s4 (wz (e_flags en)) (wz hBv) (e_sp en) (wz (e_PL en + 24)) (wz (e_BI en)) (wz LB2) (wz len) t3 t4 t5 t6)
                 (e_F en) (wz J_HD) (e_fc en) None m (seg_rom usegs))
      (pem_post en).

  Definition HD2_at (N : Z) : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig
           (xra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 l0 l3 l8 l11 ta tb : word)
           (qn ql : bptr) (namev nn LB2 hBv dBv tmpv ov got prev endv partv fl2 len : Z) (str bn2 bs : list byte) (KT KO : mbk)
           (methT methO lenT maxT lenO maxO : Z),
    e_blen en - off <= N ->
    pem_com en s LBc Lc f m off rem rA rB rBig ->
    hd_inv en LBc Lc m off rem rA rB rBig qn ql namev nn LB2 hBv dBv tmpv ov got len str bn2 bs KT KO methT methO lenT maxT lenO maxO ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 (wz tmpv) (wz namev) l3 (wz endv) (wz LB2) (wz (e_PL en + 8)) (wz (e_PL en + 16)) l8 (wz dBv) (wz (e_flags en)) l11 ta tb) ->
    (endv = 0 \/ endv = 1) -> (prev = 0 \/ prev = 1) -> (partv = 0 \/ partv = 1) -> 0 <= fl2 < 2 ^ 32 ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) (wz prev) a0 a1 (wz fl2) a3 a4 a5 a6 a7
                       (wz PEM_ENDSTR) (wz got) (wz partv) (wz (e_flags en)) (wz hBv) (e_sp en) (wz (e_PL en + 24)) (wz (e_BI en)) (wz LB2) (wz len) t3 t4 t5 t6)
                 (e_F en) (wz J_HD2) (e_fc en) None m (seg_rom usegs))
      (pem_post en).

  (* [comment removed for export] *)
  Definition J_GETS1 : Z := 0x1883f8.
  Definition J_GETS2 : Z := 0x188444.
  Definition GETS1_at (N : Z) : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig
           (xra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s10 s11 t3 t4 t5 t6 l0 l8 l11 ta tb : word)
           (qn ql : bptr) (namev nn LB2 hBv dBv tmpv ov got endv partv : Z) (str bn2 bs : list byte) (KT KO : mbk) (methT methO lenT maxT lenO maxO : Z),
    e_blen en - off <= N ->
    pem_com en s LBc Lc f m off rem rA rB rBig ->
    gets_pre en LBc Lc m off rem rA rB rBig qn ql namev nn LB2 hBv dBv tmpv ov got str bn2 bs KT KO methT methO lenT maxT lenO maxO ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 (wz tmpv) (wz namev) (wz partv) (wz endv) (wz LB2) (wz (e_PL en + 8)) (wz (e_PL en + 16)) l8 (wz dBv) (wz (e_flags en)) l11 ta tb) ->
    (endv = 0 \/ endv = 1) -> (partv = 0 \/ partv = 1) ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 (wz got) (wz PEM_ENDSTR) (wz (e_flags en)) (wz hBv) (e_sp en) (wz (e_PL en + 24)) (wz (e_BI en)) s10 s11 t3 t4 t5 t6)
                 (e_F en) (wz J_GETS1) (e_fc en) None m (seg_rom usegs))
      (pem_post en).
  Definition GETS2_at (N : Z) : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig
           (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6 l0 l3 l8 l11 ta tb : word)
           (qn ql : bptr) (namev nn LB2 hBv dBv tmpv ov got endv partv : Z) (str bn2 bs : list byte) (KT KO : mbk) (methT methO lenT maxT lenO maxO : Z),
    e_blen en - off <= N ->
    pem_com en s LBc Lc f m off rem rA rB rBig ->
    gets_pre en LBc Lc m off rem rA rB rBig qn ql namev nn LB2 hBv dBv tmpv ov got str bn2 bs KT KO methT methO lenT maxT lenO maxO ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 (wz tmpv) (wz namev) l3 (wz endv) (wz LB2) (wz (e_PL en + 8)) (wz (e_PL en + 16)) l8 (wz dBv) (wz (e_flags en)) l11 ta tb) ->
    (endv = 0 \/ endv = 1) -> (partv = 0 \/ partv = 1) ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) (wz got) a0 a1 a2 a3 a4 a5 a6 a7
                       (wz PEM_ENDSTR) s3 (wz partv) (wz (e_flags en)) (wz hBv) (e_sp en) (wz (e_PL en + 24)) (wz (e_BI en)) (wz LB2) s11 t3 t4 t5 t6)
                 (e_F en) (wz J_GETS2) (e_fc en) None m (seg_rom usegs))
      (pem_post en).

  (* [comment removed for export] *)
  Definition J_PUTS : Z := 0x1883c0.
  Definition PUTS_at (N : Z) : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig
           (xra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 l0 l4 l8 l11 ta tb : word)
           (qn ql : bptr) (namev nn LB2 hBv dBv tmpv ov got partv len' : Z) (str bn2 bs : list byte) (KT KO : mbk) (methT methO lenT maxT lenO maxO : Z),
    e_blen en - off <= N ->
    pem_com en s LBc Lc f m off rem rA rB rBig ->
    hd_core en LBc Lc m rA rB rBig qn ql namev nn LB2 hBv dBv tmpv ov got str bn2 bs KT KO methT methO lenT maxT lenO maxO ->
    (Z.to_nat (2 * (e_blen en - off) + 18) <= rem)%nat -> lenT + lenO + len' <= 2 * (off - e_boff en) -> 1 <= len' <= 255 ->
    nth_error bs (Z.to_nat len') = Some (Z_to_bv 8 0) ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 (wz tmpv) (wz namev) (wz partv) l4 (wz LB2) (wz (e_PL en + 8)) (wz (e_PL en + 16)) l8 (wz dBv) (wz (e_flags en)) l11 ta tb) ->
    (partv = 0 \/ partv = 1) ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) s1 a0 a1 a2 a3 a4 a5 a6 a7
                       (wz len') (wz got) (wz PEM_ENDSTR) (wz (e_flags en)) (wz hBv) (e_sp en) (wz (e_PL en + 24)) (wz (e_BI en)) (wz LB2) s11 t3 t4 t5 t6)
                 (e_F en) (wz J_PUTS) (e_fc en) None m (seg_rom usegs))
      (pem_post en).

  (* [comment removed for export] *)
  Definition J_FREE1 : Z := 0x188178.
  Definition FREE1_stmt : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig strs
           (xra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s9 s11 t3 t4 t5 t6 l0 l1 l2 l3 l4 l5 l6 l7 l10 l11 ta tb : word)
           (ql : bptr) (LB1 hBv dBv : Z) (bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    let curids := mbio_blocks KX ++ mbio_blocks KY ++ [ql] in
    pem_com en s LBc Lc f m off rem rA rB rBig -> pem_err en strs m -> (13 <= rem)%nat ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 l1 l2 l3 l4 l5 l6 l7 (wz hBv) (wz dBv) l10 l11 ta tb) ->
    cown LBc Lc ql LB1 256 256 -> length bs = 256%nat -> rw_cells usegs m LB1 [CB 256 bs] ->
    mbio_rep m LBc Lc KX hBv methX lenX maxX 0 -> mbio_rep m LBc Lc KY dBv methY lenY maxY 0 ->
    (forall b, In b LBc -> In b (e_LBall en) \/ In (blk_id b) curids \/ In b strs) -> incl_blocks strs LBc -> strs_inL Lc strs ->
    (forall b, In b (e_LBall en) -> ~ In (blk_id b) curids) -> (forall b, In b strs -> ~ In (blk_id b) (map blk_id (e_LBall en))) ->
    (forall q nm, In (q, nm) (e_L en) -> ~ In q curids) ->
    List.NoDup (curids ++ map blk_id strs ++ e_pe en :: mbio_blocks (e_K en)) ->
    rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 (wz (e_flags en)) s6 s7 (wz (e_PL en + 24)) s9 (wz LB1) s11 t3 t4 t5 t6) (e_F en) (wz J_FREE1) (e_fc en) None m (seg_rom usegs))
      (pem_post en).

  (* [comment removed for export] *)
  Definition J_RAISE1 : Z := 0x188148.
  Definition RAISE1_stmt : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig
           (xra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 l0 l1 l2 l3 l4 l5 l6 l7 l11 ta tb : word)
           (ql : bptr) (LB1 hBv dBv : Z) (bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
    let curids := mbio_blocks KX ++ mbio_blocks KY ++ [ql] in
    pem_com en s LBc Lc f m off rem rA rB rBig -> errst_at_rest (e_E en) [] m -> (15 <= rem)%nat -> 2 <= rA ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 l1 l2 l3 l4 l5 l6 l7 (wz hBv) (wz dBv) (wz (e_flags en)) l11 ta tb) ->
    cown LBc Lc ql LB1 256 256 -> length bs = 256%nat -> rw_cells usegs m LB1 [CB 256 bs] ->
    mbio_rep m LBc Lc KX hBv methX lenX maxX 0 -> mbio_rep m LBc Lc KY dBv methY lenY maxY 0 ->
    (forall b, In b LBc -> In b (e_LBall en) \/ In (blk_id b) curids) ->
    (forall b, In b (e_LBall en) -> ~ In (blk_id b) curids) -> (forall q nm, In (q, nm) (e_L en) -> ~ In q curids) ->
    List.NoDup (curids ++ e_pe en :: mbio_blocks (e_K en)) ->
    rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 (wz (e_PL en + 24)) s9 (wz LB1) s11 t3 t4 t5 t6) (e_F en) (wz J_RAISE1) (e_fc en) None m (seg_rom usegs))
      (pem_post en).

  (* [comment removed for export] *)
  Definition J_NGETS : Z := 0x1882c8.
  Definition NGETS_stmt : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig
           (xra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s11 t3 t4 t5 t6 l0 l1 l3 l4 l5 l11 ta tb : word)
           (qn ql : bptr) (namev nn LB2 hBv dBv : Z) (str bn2 bs : list byte) (KX KY : mbk) (methX methY : Z),
    let curids := mbio_blocks KX ++ mbio_blocks KY ++ [qn; ql] in
    pem_com en s LBc Lc f m off rem rA rB rBig -> errst_at_rest (e_E en) [] m ->
    (Z.to_nat (2 * (e_blen en - off) + 16) <= rem)%nat -> 0 <= e_boff en -> e_blen en < 2 ^ 26 ->
    5 <= rA -> 4 <= rB -> 6 * (e_blen en - e_boff en) + 32778 <= rBig ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 l1 (wz namev) l3 l4 l5 (wz (e_PL en + 8)) (wz (e_PL en + 16)) (wz hBv) (wz dBv) (wz (e_flags en)) l11 ta tb) ->
    cown LBc Lc qn namev nn nn -> 1 <= nn <= 239 -> length (str ++ Z_to_bv 8 0 :: bn2) = Z.to_nat nn ->
    rw_cells usegs m namev [CB (Z.to_nat nn) (str ++ Z_to_bv 8 0 :: bn2)] -> ~ In (Z_to_bv 8 0) str ->
    cown LBc Lc ql LB2 256 256 -> length bs = 256%nat -> rw_cells usegs m LB2 [CB 256 bs] ->
    mbio_rep m LBc Lc KX hBv methX 0 0 0 -> k_d KX = None -> mbio_rep m LBc Lc KY dBv methY 0 0 0 -> k_d KY = None ->
    (forall b, In b LBc -> In b (e_LBall en) \/ In (blk_id b) curids) ->
    (forall b, In b (e_LBall en) -> ~ In (blk_id b) curids) -> (forall q nm, In (q, nm) (e_L en) -> ~ In q curids) ->
    List.NoDup (curids ++ e_pe en :: mbio_blocks (e_K en)) ->
    rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 (wz (e_flags en)) s6 (e_sp en) (wz (e_PL en + 24)) (wz (e_BI en)) (wz LB2) s11 t3 t4 t5 t6) (e_F en) (wz J_NGETS) (e_fc en) None m (seg_rom usegs))
      (pem_post en).

  (* [comment removed for export] *)
  Definition J_NAME : Z := 0x18824c.
  Definition NAME_stmt : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig
           (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 l0 l1 l2 l3 l4 l5 l11 ta tb : word)
           (ql : bptr) (LB1 hBv dBv len' : Z) (bs : list byte) (KX KY : mbk) (methX methY : Z),
    let curids := mbio_blocks KX ++ mbio_blocks KY ++ [ql] in
    pem_com en s LBc Lc f m off rem rA rB rBig -> errst_at_rest (e_E en) [] m ->
    (Z.to_nat (2 * (e_blen en - off) + 19) <= rem)%nat -> 0 <= e_boff en -> e_blen en < 2 ^ 26 ->
    6 <= rA -> 5 <= rB -> 6 * (e_blen en - e_boff en) + 32778 + 8448 <= rBig ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 l1 l2 l3 l4 l5 (wz (e_PL en + 8)) (wz (e_PL en + 16)) (wz hBv) (wz dBv) (wz (e_flags en)) l11 ta tb) ->
    cown LBc Lc ql LB1 256 256 -> length bs = 256%nat -> rw_cells usegs m LB1 [CB 256 bs] -> 17 <= len' <= 255 ->
    mbio_rep m LBc Lc KX hBv methX 0 0 0 -> k_d KX = None -> mbio_rep m LBc Lc KY dBv methY 0 0 0 -> k_d KY = None ->
    (forall b, In b LBc -> In b (e_LBall en) \/ In (blk_id b) curids) ->
    (forall b, In b (e_LBall en) -> ~ In (blk_id b) curids) -> (forall q nm, In (q, nm) (e_L en) -> ~ In q curids) ->
    List.NoDup (curids ++ e_pe en :: mbio_blocks (e_K en)) ->
    rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) (wz (2 ^ 64 - 1 - LB1)) a0 a1 a2 a3 a4 a5 a6 a7
                       (wz len') s3 s4 s5 s6 (e_sp en) (wz (e_PL en + 24)) (wz (e_BI en)) (wz LB1) s11 t3 t4 t5 t6) (e_F en) (wz J_NAME) (e_fc en) None m (seg_rom usegs))
      (pem_post en).

  (* [comment removed for export] *)
  Definition J_GN : Z := 0x1880dc.
  Definition J_GNG : Z := 0x18812c.
  Definition GN_at (N : Z) : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig
           (xra t0 t1 t2 a0 a2 a4 a5 a6 a7 s2 t3 t4 t5 t6 l0 l1 l2 l3 l4 l5 l11 ta tb : word)
           (ql : bptr) (LB1 hBv dBv len fc fl : Z) (bs : list byte) (KX KY : mbk) (methX methY : Z),
    let curids := mbio_blocks KX ++ mbio_blocks KY ++ [ql] in
    e_blen en - off <= N ->
    pem_com en s LBc Lc f m off rem rA rB rBig -> errst_at_rest (e_E en) [] m ->
    (Z.to_nat (2 * (e_blen en - off) + 19) <= rem)%nat -> 0 <= e_boff en -> e_blen en < 2 ^ 26 ->
    6 <= rA -> 5 <= rB -> 6 * (e_blen en - e_boff en) + 32778 + 8448 <= rBig ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 l1 l2 l3 l4 l5 (wz (e_PL en + 8)) (wz (e_PL en + 16)) (wz hBv) (wz dBv) (wz (e_flags en)) l11 ta tb) ->
    cown LBc Lc ql LB1 256 256 -> length bs = 256%nat -> rw_cells usegs m LB1 [CB 256 bs] ->
    1 <= len <= 254 -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) -> 0 <= fc < 2 ^ 32 -> 0 <= fl < 2 ^ 32 ->
    mbio_rep m LBc Lc KX hBv methX 0 0 0 -> k_d KX = None -> mbio_rep m LBc Lc KY dBv methY 0 0 0 -> k_d KY = None ->
    (forall b, In b LBc -> In b (e_LBall en) \/ In (blk_id b) curids) ->
    (forall b, In b (e_LBall en) -> ~ In (blk_id b) curids) -> (forall q nm, In (q, nm) (e_L en) -> ~ In q curids) ->
    List.NoDup (curids ++ e_pe en :: mbio_blocks (e_K en)) ->
    rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) (wz (2 ^ 64 - 1 - LB1)) a0 (wz len) a2 (wz fc) a4 a5 a6 a7
                       s2 (wz 0x341ae) (wz fl) (wz 6) (wz 7) (e_sp en) (wz (e_PL en + 24)) (wz (e_BI en)) (wz LB1) (wz 0x20527) t3 t4 t5 t6)
                 (e_F en) (wz J_GN) (e_fc en) None m (seg_rom usegs))
      (pem_post en).
  Definition GNG_at (N : Z) : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig
           (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 l0 l1 l2 l3 l4 l5 l11 ta tb : word)
           (ql : bptr) (LB1 hBv dBv fl : Z) (bs : list byte) (KX KY : mbk) (methX methY : Z),
    let curids := mbio_blocks KX ++ mbio_blocks KY ++ [ql] in
    e_blen en - off <= N ->
    pem_com en s LBc Lc f m off rem rA rB rBig -> errst_at_rest (e_E en) [] m ->
    (Z.to_nat (2 * (e_blen en - off) + 19) <= rem)%nat -> 0 <= e_boff en -> e_blen en < 2 ^ 26 ->
    6 <= rA -> 5 <= rB -> 6 * (e_blen en - e_boff en) + 32778 + 8448 <= rBig ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 l1 l2 l3 l4 l5 (wz (e_PL en + 8)) (wz (e_PL en + 16)) (wz hBv) (wz dBv) (wz (e_flags en)) l11 ta tb) ->
    cown LBc Lc ql LB1 256 256 -> length bs = 256%nat -> rw_cells usegs m LB1 [CB 256 bs] ->
    0 <= fl < 2 ^ 32 ->
    mbio_rep m LBc Lc KX hBv methX 0 0 0 -> k_d KX = None -> mbio_rep m LBc Lc KY dBv methY 0 0 0 -> k_d KY = None ->
    (forall b, In b LBc -> In b (e_LBall en) \/ In (blk_id b) curids) ->
    (forall b, In b (e_LBall en) -> ~ In (blk_id b) curids) -> (forall q nm, In (q, nm) (e_L en) -> ~ In q curids) ->
    List.NoDup (curids ++ e_pe en :: mbio_blocks (e_K en)) ->
    rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) (wz (2 ^ 64 - 1 - LB1)) a0 a1 a2 a3 a4 a5 a6 a7
                       s2 (wz 0x341ae) (wz fl) (wz 6) (wz 7) (e_sp en) (wz (e_PL en + 24)) (wz (e_BI en)) (wz LB1) (wz 0x20527) t3 t4 t5 t6)
                 (e_F en) (wz J_GNG) (e_fc en) None m (seg_rom usegs))
      (pem_post en).
End W3.
