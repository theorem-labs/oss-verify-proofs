(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr SysStep.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF AllocSpec SReach.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc HttpAllocX.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_syscalls H_obj H_prep H_map_str_to_int H_httpmsg_destroy
     H_membuffer_assign H_parse_uri_A H_UpnpPrintf H_pent_A H_pent_B H_phdr_B.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.

Definition parser_parse_entry : Z := 0x15bec.
Definition PP_JOIN : Z := 0x15c98.
Definition PP_HEAD : Z := 0x15c9c.
Definition PP_REQL : Z := 0x15cb8.
Definition PP_EXIT : Z := 0x15fe0.
Definition PP_FRAME : Z := 208.

Notation METHOD_TAB := 0x2b3b8%Z.
Notation FMT_REQ09 := 0x10331%Z.
Notation FMT_REQ := 0x10423%Z.

Definition PP_DEPTH : Z := 4096.
Definition PP_ADEPTH : Z := 4096.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Notation L_ := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Notation hdr := (hdr AI).

  Record pstate := mkPS {
    ps_cur : Z;
    ps_A : Z; ps_len : Z; ps_cap : Z; ps_okm : option K; ps_bs : list byte;
    ps_meth : Z;
    ps_uc : list cell;
    ps_rm : Z; ps_sc : Z;
    ps_SA : Z; ps_slen : Z; ps_scap : Z; ps_sok : option K; ps_sbs : list byte;
    ps_isreq : Z; ps_maj : Z; ps_min : Z;
    ps_ns : list (BLK * Z); ps_hs : list hdr; ps_X : Z;
    ps_ebw : word; ps_elw : word;
    ps_err : Z; ps_hack : Z; ps_pos : Z; ps_entp : Z; ps_clen : Z; ps_csz : Z; ps_esp : Z;
    ps_ub : Z; ps_UB : list BLK
  }.

  Definition ps_blocks (st : pstate) : list BLK :=
    hl_blocks AI (ps_ns st) (ps_hs st) ++ okb AI (ps_okm st) (ps_A st) (ps_cap st)
    ++ okb AI (ps_sok st) (ps_SA st) (ps_scap st) ++ ps_UB st.

  Definition p_smsgw (m : mem) (LB : list BLK) (P SA slen scap : Z) (sok : option K) (sbs : list byte) : Prop :=
    rw_cells rsegs m (P + 232) (mbuf_cells SA slen scap) /\ mown AI m LB SA scap sok sbs /\ 0 <= slen <= scap /\ scap < 2^32.

  Definition p_methw (m : mem) (P meth : Z) : Prop := rw_cells rsegs m P [C4 (wz 1); C4 (wz meth)] /\ 0 <= meth <= 12.

  Definition p_parser (m : mem) (LB : list BLK) (P : Z) (st : pstate) : Prop :=
    p_scan m P (ps_cur st)
    /\ p_msg AI m LB P (ps_A st) (ps_len st) (ps_cap st) (ps_okm st) (ps_bs st) /\ 0 <= ps_cur st <= ps_len st
    /\ p_methw m P (ps_meth st) /\ p_uri m P (ps_uc st) /\ p_rs m P (ps_rm st) (ps_sc st)
    /\ p_smsgw m LB P (ps_SA st) (ps_slen st) (ps_scap st) (ps_sok st) (ps_sbs st)
    /\ p_ver m P (ps_isreq st) (ps_maj st) (ps_min st)
    /\ p_hlist AI m P (ps_ns st) (ps_hs st) (ps_X st) /\ ps_X st <= VMAX
    /\ p_ent m P (ps_ebw st) (ps_elw st)
    /\ p_ctl m P (ps_err st) (ps_hack st) (ps_pos st) (ps_entp st) (ps_clen st) (ps_csz st) (ps_esp st)
    /\ H_prep.p_url m P (ps_ub st) /\ ubo AI (ps_ub st) (ps_UB st).

  Definition pp_side (gmax : Z) (st : pstate) : Prop :=
    ps_X st + 2 * (ps_len st - ps_cur st) <= VMAX
    /\ (ps_pos st = POS_ENTITY -> ps_okm st <> None /\ ent_ok gmax (ps_entp st) (ps_cur st) (ps_esp st) (ps_csz st) (ps_elw st))
    /\ (ps_pos st <> POS_ENTITY -> ps_entp st = 1)
    /\ (ps_pos st = POS_RESPONSE_LINE -> ps_scap st + 1 <= LMAX
                                         /\ (ps_sok st <> None -> nth_error (ps_sbs st) (Z.to_nat (ps_slen st)) = Some (Z_to_bv 8 0)))
    /\ (ps_pos st <> POS_COMPLETE -> ps_meth st <= 11).

  Definition pp_stat (m : mem) (gmax : Z) (gifv : word) (ws mws : list word) : Prop :=
    u64arr rsegs m TAB_HDR ws /\ (exists zb, bytes_at rsegs m ZERO_ADDR [zb])
    /\ u64arr rsegs m METHOD_TAB mws
    /\ bytes_at rsegs m GOT_GIF (le8 (wz GIF)) /\ bytes_at rsegs m GIF (le4 gifv)
    /\ rw_cells rsegs m GMAXA [C8 (wz gmax)] /\ rw_cells rsegs m INITWASCALLED [C1 (Z_to_bv 8 0)]
    /\ bytes_at rsegs m GOT_GMAX (le8 (wz GMAXA)).

  Definition hdr_tab_ok (ws : list word) (Blo : Z) : Prop :=
    length ws = 66%nat
    /\ (forall i, 0 <= i < 33 -> exists id, nth_error ws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ 0 <= id < 64)
    /\ table_strings ws 33 Blo.
  Definition meth_tab_ok (mws : list word) (Blo : Z) : Prop :=
    length mws = 22%nat
    /\ (forall i, 0 <= i < 11 -> exists id, nth_error mws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ 0 <= id <= 11)
    /\ table_strings mws 11 Blo.

  Definition pp_W (P : Z) : list ivl := [(P, P + 500)].

  Definition pp_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (P lo B gmax : Z) (gifv : word) (ws mws : list word) (LBK : list BLK) (isreq : Z) (m0 : mem)
      : ai_PS rsegs AI -> list BLK -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z) (st' : pstate),
      ms' = MS (mkR ra sp gp (wz (al_tp L_)) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ RENV rsegs AI m' B
      /\ (exists e, rw_cells rsegs m' (al_errno L_) [C4 e])
      /\ hpx AI (pp_W P) LBK (bv_unsigned sp) m0 m'
      /\ RHEAP rsegs AI s' LB' m'
      /\ p_parser m' LB' P st' /\ ps_isreq st' = isreq
      /\ bsub AI (ps_blocks st' ++ LBK) LB' /\ NoDup (map blk_id (ps_blocks st' ++ LBK))
      /\ pp_stat m' gmax gifv ws mws
      /\ 0 <= r <= 5.

  Section FRAME.
    Variables (P q lo B gmax : Z) (gifv : word) (ws mws : list word) (LBK : list BLK) (m0 : mem).
    Variables (ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word).

    Definition pp_st (pc : Z) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
        : machine_state :=
      MS (mkR x1 (wz q) gp (wz (al_tp L_)) t0 t1 t2 (wz P) (wz (P + 480)) a0 a1 a2 a3 a4 a5 a6 a7
              (wz (-1)) (wz 47) (wz 2) (wz FMT_REQ09) (wz METHOD_TAB) s7v (wz 3) s9v (wz 1) (wz 4) t3 t4 t5 t6)
         F (wz pc) fc None m (seg_rom rsegs).

    Definition ppFS : list cell :=
      [C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

    Definition ppFX (m : mem) : Prop :=
      (exists j1, rw_cells rsegs m q [CB 16 j1])
      /\ rw_cells rsegs m (q + 16) [C8 (wz (P + 280)); C8 (wz (P + 276)); C8 (wz (P + 8)); C8 (wz (2^64 - 1 - METHOD_TAB)); C8 (wz FMT_REQ)]
      /\ (exists j2, rw_cells rsegs m (q + 56) [CB 48 j2]).

    Definition pp_core (s : ai_PS rsegs AI) (LB : list BLK) (m : mem) (st : pstate) : Prop :=
      RHEAP rsegs AI s LB m /\ RENV rsegs AI m B /\ mem_inv rsegs m /\ stk rsegs m lo q
      /\ (exists e, rw_cells rsegs m (al_errno L_) [C4 e])
      /\ rw_cells rsegs m (q + 104) ppFS /\ ppFX m
      /\ p_parser m LB P st
      /\ bsub AI (ps_blocks st ++ LBK) LB /\ NoDup (map blk_id (ps_blocks st ++ LBK))
      /\ pp_stat m gmax gifv ws mws
      /\ hpx AI (pp_W P) LBK (q + 208) m0 m.

    Definition reql_post (gp : word) (F : bvmap 5 word) (fc : bv 32) (st : pstate)
        : ai_PS rsegs AI -> list BLK -> machine_state -> Prop :=
      fun s' LB' ms' => exists x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 m' (r : Z) (st' : pstate),
        ms' = pp_st PP_JOIN x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m'
        /\ pp_core s' LB' m' st' /\ ps_isreq st' = ps_isreq st
        /\ 0 <= r <= 5
        /\ (r = 4 -> ps_pos st' = POS_HEADERS /\ pp_side gmax st').

    Definition reql_arm : Prop :=
      forall s LB m (st : pstate) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp (F : bvmap 5 word) fc,
        pp_core s LB m st -> pp_side gmax st -> ps_pos st = POS_REQUEST_LINE ->
        SREACH AI (reql_post gp F fc st) (pp_st PP_REQL x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m) s LB.
  End FRAME.
End W.

Arguments mkPS {HCEIL AI}.
Arguments ps_cur {HCEIL AI}.
Arguments ps_A {HCEIL AI}.
Arguments ps_len {HCEIL AI}.
Arguments ps_cap {HCEIL AI}.
Arguments ps_okm {HCEIL AI}.
Arguments ps_bs {HCEIL AI}.
Arguments ps_meth {HCEIL AI}.
Arguments ps_uc {HCEIL AI}.
Arguments ps_rm {HCEIL AI}.
Arguments ps_sc {HCEIL AI}.
Arguments ps_SA {HCEIL AI}.
Arguments ps_slen {HCEIL AI}.
Arguments ps_scap {HCEIL AI}.
Arguments ps_sok {HCEIL AI}.
Arguments ps_sbs {HCEIL AI}.
Arguments ps_isreq {HCEIL AI}.
Arguments ps_maj {HCEIL AI}.
Arguments ps_min {HCEIL AI}.
Arguments ps_ns {HCEIL AI}.
Arguments ps_hs {HCEIL AI}.
Arguments ps_X {HCEIL AI}.
Arguments ps_ebw {HCEIL AI}.
Arguments ps_elw {HCEIL AI}.
Arguments ps_err {HCEIL AI}.
Arguments ps_hack {HCEIL AI}.
Arguments ps_pos {HCEIL AI}.
Arguments ps_entp {HCEIL AI}.
Arguments ps_clen {HCEIL AI}.
Arguments ps_csz {HCEIL AI}.
Arguments ps_esp {HCEIL AI}.
Arguments ps_ub {HCEIL AI}.
Arguments ps_UB {HCEIL AI}.

Definition reql_stmt {HCEIL : HasCeiling} (AI : alloc_if rsegs) : Prop :=
  forall (P q lo B gmax : Z) (gifv : word) (ws mws : list word) (LBK : list (block (ai_K rsegs AI))) (m0 : mem)
         (ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word),
    lo + PP_DEPTH <= q + 208 -> lo <= q + 208 - PP_ADEPTH - al_stack (ai_L rsegs AI) -> 0 <= al_stack (ai_L rsegs AI) ->
    0x5d000 <= lo -> alloc_ceiling <= lo -> q + 208 <= P -> P + 504 <= B -> B < 2^62 -> P mod 8 = 0 -> (q + 208) mod 16 = 0 ->
    hdr_tab_ok ws lo -> meth_tab_ok mws lo -> 0 < gmax < 2^32 ->
    reql_arm AI P q lo B gmax gifv ws mws LBK m0 ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e.

Definition pp_rank (pos : Z) : Z :=
  if (pos <=? 1)%Z then 3 else if (pos =? 2)%Z then 2 else if (pos =? 3)%Z then 1 else 0.

Definition parser_parse_stmt {HCEIL : HasCeiling} (AI : alloc_if rsegs) : Prop :=
  forall (P lo B gmax : Z) (gifv : word) (ws mws : list word) (LBK : list (block (ai_K rsegs AI))) (st : pstate AI)
         (s : ai_PS rsegs AI) (LB : list (block (ai_K rsegs AI)))
         (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (e : word),

    lo + PP_DEPTH <= bv_unsigned sp -> lo <= bv_unsigned sp - PP_ADEPTH - al_stack (ai_L rsegs AI) -> 0 <= al_stack (ai_L rsegs AI) ->
    0x5d000 <= lo -> alloc_ceiling <= lo ->
    bv_unsigned sp <= P -> P + 504 <= B -> B < 2^62 -> P mod 8 = 0 -> bv_unsigned sp mod 16 = 0 ->
    hdr_tab_ok ws lo -> meth_tab_ok mws lo -> 0 < gmax < 2^32 ->

    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
    rw_cells rsegs m (al_errno (ai_L rsegs AI)) [C4 e] ->
    p_parser AI m LB P st -> pp_side AI gmax st ->
    bsub AI (ps_blocks AI st ++ LBK) LB -> NoDup (map blk_id (ps_blocks AI st ++ LBK)) ->
    pp_stat m gmax gifv ws mws ->
    a0 = wz P ->
    SREACH AI (pp_post AI ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P lo B gmax gifv ws mws LBK (ps_isreq st) m)
      (MS (mkR ra sp gp (wz (al_tp (ai_L rsegs AI))) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz parser_parse_entry) fc None m (seg_rom rsegs)) s LB.
