(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmCurDefs_u.
Import ListNotations.
Import PML.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMS.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable STRTOD_SCR : Z.

Definition OPNEW_SCR : Z := 16 + HEAP_STACK.
Definition OPDEL_SCR : Z := HEAP_STACK.
Definition STR_SCR : Z := 256 + OPNEW_SCR.
Definition VEC_SCR : Z := 128 + OPNEW_SCR.
Definition SETEC_SCR : Z := 256.
Definition PF_SCR : Z := 1024 + Z.max OPNEW_SCR STRTOD_SCR.
Definition ESV_SCR : Z := 512.
Definition CONVERT_SCR : Z := 112 + STR_SCR.
Definition APPEND_CP_SCR : Z := 48 + SETEC_SCR.
Definition AFTERV_SCR : Z := 512.
Definition ENDNUM_SCR : Z := 512 + Z.max 256 STRTOD_SCR.
Definition PSOME_SCR : Z := 128 + PF_SCR.

Definition SKIPWS_SCR : Z := 80 + PF_SCR.
Definition READNEXT_SCR : Z := 80 + 64 + PSOME_SCR.
Definition READ_SCR : Z := 32 + READNEXT_SCR.
Definition CTOR_SCR : Z := 1024 + OPNEW_SCR.
Definition ISLAND_SCR : Z := 4096.
Definition ISS_SCR : Z := 80 + Z.max CTOR_SCR ISLAND_SCR.
Definition RCTOR_SCR : Z := 304 + CTOR_SCR.

Definition LIB_SCR : Z := 928 + Z.max READ_SCR (Z.max RCTOR_SCR ISS_SCR).

Definition opnew_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (n sp r : Z),
    cps_heap L HI PC_OPNEW r sp OPNEW_SCR LB cr
      (fun R M => entry L R M sp r OPNEW_SCR /\ a0 R n /\ 0 < n <= 2 ^ 27 /\ credit_ok L cr n)
      (fun R M R' M' LB' cr' LBk W => exists A, a0 R' A /\ L5C.fresh_block L LB M' A n /\ LB' = (A, n) :: LB /\ cr' = debit L cr n /\ LBk = LB /\ W = []).

Definition opdel_spec_at (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (A n sp r : Z),
    cps_heap L HI pc r sp OPDEL_SCR LB cr
      (fun R M => entry L R M sp r OPDEL_SCR /\ a0 R A /\ In (A, n) LB)
      (fun R M R' M' LB' cr' LBk W => LB' = lb_remove A LB /\ cr' = cr /\ LBk = lb_remove A LB /\ W = []).
Definition opdel_spec := opdel_spec_at PC_OPDEL.
Definition opdel_sized_spec := opdel_spec_at PC_OPDEL_SIZED.

Definition guard_acquire_spec : Prop :=
  forall (G sp r : Z),
    cps_pure PC_GUARD_ACQ r sp 0 [(G, 2)]
      (fun R M => entry L R M sp r 0 /\ a0 R G /\ 0 <= G < 2 ^ 62   /\
                  u8 M G 0 /\ u8 M (G + 1) 0 /\ L5.writable RSEGS M G 2)
      (fun R M R' M' => a0 R' 1 /\ u8 M' G 0 /\ u8 M' (G + 1) 2).
Definition guard_release_spec : Prop :=
  forall (G sp r : Z),
    cps_pure PC_GUARD_REL r sp 0 [(G, 2)]
      (fun R M => entry L R M sp r 0 /\ a0 R G /\ 0 <= G < 2 ^ 62   /\ L5.writable RSEGS M G 2)
      (fun R M R' M' => u8 M' G 1 /\ u8 M' (G + 1) 1).

Definition system_category_spec : Prop :=
  forall (sp r : Z),
    cps_pure PC_SYSTEM_CATEGORY r sp 64 [(0xd5030, 2)]
      (fun R M => entry L R M sp r 64 /\ img_ro M /\ ((u8 M 0xd5030 0 /\ u8 M 0xd5031 0) \/ u8 M 0xd5030 1))
      (fun R M R' M' => a0 R' OBJ_SYSTEM_CATEGORY /\ u8 M' 0xd5030 1).

Definition cxa_atexit_spec : Prop :=
  forall (f a dso sp r : Z),
    cps_pure PC_CXA_ATEXIT r sp 128 [(0xf6848, 544)]
      (fun R M => entry L R M sp r 128 /\ a0 R f /\ a1 R a /\ a2 R dso /\ atexit_cells M [] /\ L5.writable RSEGS M 0xf6848 544 /\ libc_quiet M  )
      (fun R M R' M' => a0 R' 0 /\ atexit_cells M' [(f, a)]).

Definition cxa_atexit2_spec : Prop :=
  forall (f a dso sp r : Z) (h : Z * Z),
    cps_pure PC_CXA_ATEXIT r sp 128 [(0xf6848, 544)]
      (fun R M => entry L R M sp r 128 /\ a0 R f /\ a1 R a /\ a2 R dso /\ atexit_cells M [h] /\ L5.writable RSEGS M 0xf6848 544 /\ libc_quiet M)
      (fun R M R' M' => a0 R' 0 /\ atexit_cells M' [h; (f, a)]).

Definition strtod_spec : Prop :=
  forall (s endp sp r : Z) (txt : list Z),
    cps_pure PC_STRTOD r sp STRTOD_SCR [(endp, 8); (TP - 164, 4)]
      (fun R M => entry L R M sp r STRTOD_SCR /\ a0 R s /\ a1 R endp /\ img_ro M /\
                  L5.bytes_at RSEGS M s txt /\ u8 M (s + Z.of_nat (length txt)) 0 /\ num_final txt /\ Z.of_nat (length txt) < 2 ^ 26 /\
                  L5.defined M endp 8 /\ sp <= endp /\ endp + 8 <= hl_sptop L /\

                  (s + Z.of_nat (length txt) + 1 <= sp - STRTOD_SCR \/ sp <= s) /\
                  (s + Z.of_nat (length txt) + 1 <= endp \/ endp + 8 <= s) /\
                  (s + Z.of_nat (length txt) + 1 <= TP - 164 \/ TP - 160 <= s) /\

                  L5.defined M s (Z.of_nat (length txt) + 1) /\

                  4096 <= s   /\ s + Z.of_nat (length txt) < 2 ^ 47)
      (fun R M R' M' => u64 M' endp (s + Z.of_nat (length txt))).

Definition str_reserve_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (o sp r : Z),
    cps_heap L HI PC_STR_RESERVE r sp STR_SCR LB cr
      (fun R M => entry L R M sp r STR_SCR /\ a0 R o /\ a1 R 256 /\ u64 M o 0 /\ u64 M (o + 8) 0 /\ u64 M (o + 16) 0 /\ obj_on_stack L sp o 24 /\ credit_ok L cr 264)
      (fun R M R' M' LB' cr' LBk W => exists p, str_at M' o (SLong 264 p []) /\ L5C.fresh_block L LB M' p 264 /\
                                                LB' = (p, 264) :: LB /\ cr' = debit L cr 264 /\ LBk = LB /\ W = [(o, 24)]).

Definition str_grown (LB : list (Z * Z)) (cr : credit) (M' : mem) (o cap p : Z) (s' : list Z)
           (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) : Prop :=
     (str_at M' o (SLong cap p s') /\ LB' = LB /\ cr' = cr /\ LBk = lb_remove p LB)
  \/ (exists p', let cap' := grow_cap cap (Z.of_nat (length s')) in
        cap <= Z.of_nat (length s')   /\
        str_at M' o (SLong cap' p' s') /\ L5C.fresh_block L LB M' p' cap' /\
        LB' = (p', cap') :: lb_remove p LB /\ cr' = debit L cr cap' /\ LBk = lb_remove p LB).

Definition str_push_back_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (o cap p c sp r : Z) (s : list Z),
    cps_heap L HI PC_STR_PUSH_BACK r sp STR_SCR LB cr
      (fun R M => entry L R M sp r STR_SCR /\ a0 R o /\ a1 R c /\ 0 <= c < 256 /\ str_at M o (SLong cap p s) /\ 24 <= cap   /\ In (p, cap) LB /\ obj_on_stack L sp o 24 /\
                  Z.of_nat (length s) < 2 ^ 26 /\ (cap <= Z.of_nat (length s) + 1 -> credit_ok L cr (grow_cap cap (Z.of_nat (length s) + 1))))
      (fun R M R' M' LB' cr' LBk W => str_grown LB cr M' o cap p (s ++ [c]) LB' cr' LBk /\ W = [(o, 24)]).

Definition str_append_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (o cap p q sp r : Z) (s src : list Z),
    cps_heap L HI PC_STR_APPEND r sp STR_SCR LB cr
      (fun R M => entry L R M sp r STR_SCR /\ a0 R o /\ a1 R q /\ a2 R (Z.of_nat (length src)) /\
                  str_at M o (SLong cap p s) /\ 24 <= cap   /\ In (p, cap) LB /\ obj_on_stack L sp o 24 /\
                  L5.bytes_at RSEGS M q src /\ L5.defined M q (Z.of_nat (length src)) /\
                  (src = [] \/ exists b, In b LB /\ fst b <> p /\ fst b <= q /\ q + Z.of_nat (length src) <= fst b + snd b) /\
                  Z.of_nat (length s) + Z.of_nat (length src) < 2 ^ 26 /\
                  (cap <= Z.of_nat (length s) + Z.of_nat (length src) -> credit_ok L cr (grow_cap cap (Z.of_nat (length s) + Z.of_nat (length src)))))
      (fun R M R' M' LB' cr' LBk W => str_grown LB cr M' o cap p (s ++ src) LB' cr' LBk /\ W = [(o, 24)]).

Definition str_append_range_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (o cap p q sp r : Z) (s src : list Z),
    cps_heap L HI PC_APPEND_RANGE r sp STR_SCR LB cr
      (fun R M => entry L R M sp r STR_SCR /\ a0 R o /\ a1 R q /\ a2 R (q + Z.of_nat (length src)) /\
                  str_at M o (SLong cap p s) /\ 24 <= cap   /\ In (p, cap) LB /\ obj_on_stack L sp o 24 /\
                  L5.bytes_at RSEGS M q src /\ L5.defined M q (Z.of_nat (length src)) /\
                  (exists b, In b LB /\ fst b <> p /\ fst b <= q /\ q + Z.of_nat (length src) <= fst b + snd b) /\
                  Z.of_nat (length s) + Z.of_nat (length src) < 2 ^ 26 /\
                  (cap <= Z.of_nat (length s) + Z.of_nat (length src) -> credit_ok L cr (grow_cap cap (Z.of_nat (length s) + Z.of_nat (length src)))))
      (fun R M R' M' LB' cr' LBk W => str_grown LB cr M' o cap p (s ++ src) LB' cr' LBk /\ W = [(o, 24)]).

Definition vec_reserve_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (o sp r : Z),
    cps_heap L HI PC_VEC_RESERVE r sp VEC_SCR LB cr
      (fun R M => entry L R M sp r VEC_SCR /\ a0 R o /\ a1 R 66 /\ u64 M o 0 /\ u64 M (o + 8) 0 /\ u64 M (o + 16) 0 /\ obj_on_stack L sp o 24 /\ credit_ok L cr 66)
      (fun R M R' M' LB' cr' LBk W => exists b, u64 M' o b /\ u64 M' (o + 8) b /\ u64 M' (o + 16) (b + 66) /\ L5C.fresh_block L LB M' b 66 /\
                                                LB' = (b, 66) :: LB /\ cr' = debit L cr 66 /\ LBk = LB /\ W = [(o, 24)]).

Definition vec_push_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (o b cap xa x sp r : Z) (st : list Z),
    cps_heap L HI PC_VEC_PUSH r sp VEC_SCR LB cr
      (fun R M => entry L R M sp r VEC_SCR /\ a0 R o /\ a1 R xa /\ u8 M xa x /\ sp <= xa < hl_sptop L /\
                  u64 M o b /\ u64 M (o + 8) (b + Z.of_nat (length st)) /\ u64 M (o + 16) (b + cap) /\ L5.bytes_at RSEGS M b st /\
                  In (b, cap) LB /\ Z.of_nat (length st) <= cap /\ (length st <= 1026)%nat /\ obj_on_stack L sp o 24 /\ (Z.of_nat (length st) = cap -> credit_ok L cr (2 * cap)))
      (fun R M R' M' LB' cr' LBk W => W = [(o, 24)] /\
          ((Z.of_nat (length st) < cap /\ u64 M' o b /\ u64 M' (o + 8) (b + Z.of_nat (length st) + 1) /\ u64 M' (o + 16) (b + cap) /\
            L5.bytes_at RSEGS M' b (st ++ [x]) /\ LB' = LB /\ cr' = cr /\ LBk = lb_remove b LB)
        \/ (Z.of_nat (length st) = cap /\ exists b', u64 M' o b' /\ u64 M' (o + 8) (b' + cap + 1) /\ u64 M' (o + 16) (b' + 2 * cap) /\
            L5.bytes_at RSEGS M' b' (st ++ [x]) /\ L5C.fresh_block L LB M' b' (2 * cap) /\
            LB' = (b', 2 * cap) :: lb_remove b LB /\ cr' = debit L cr (2 * cap) /\ LBk = lb_remove b LB))).

Definition W_parc (P V E : Z) : list L5.range := W_par P E ++ [(V + 8, 40)].

Lemma hpres_mono : forall LBk sp scr W W' (M M' : mem), (forall a, L5.outside W' a -> L5.outside W a) -> L5C.hpres L LBk sp scr W M M' -> L5C.hpres L LBk sp scr W' M M'.
Proof. intros LBk sp scr W W' M M' HW (H1 & H2 & H3). split; [|split; [exact H2 | exact H3]]. intros a (Ha & Hc & He & Ho). apply H1. split; [exact Ha|]. split; [exact Hc|]. split; [exact He | exact (HW a Ho)]. Qed.
Lemma outside_app_l : forall W X a, L5.outside (W ++ X) a -> L5.outside W a.
Proof. intros W X a H r Hr. apply H. apply in_or_app. left. exact Hr. Qed.
Lemma W_parc_out : forall P V E a, L5.outside (W_parc P V E) a -> L5.outside (W_par P E) a.
Proof. intros P V E a. apply outside_app_l. Qed.
Definition ptrans_gb (WFin : pstate -> Prop) (BBin : pstate -> Z -> Prop) (PAin : mem -> Z -> pstate -> Prop) (PAout : pstate -> mem -> Z -> pstate -> Prop)
           (pc scr : Z) (Args : bvmap 5 word -> mem -> Z -> Z -> Z -> pstate -> Prop)
           (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r P V E B kx bx : Z) (g : ls_state) (ps : pstate),
    cps_heap L HI pc r sp scr (ps_blocks ps ++ LBo) cr
      (fun R M => entry L R M sp r scr /\ Args R M P V E ps /\
                  PAin M P ps /\ WFin ps /\ win_ok M LBo ps /\ BBin ps B /\ vis_at M V /\ ec_at M E 0 /\ ls_ok g M /\ g <> LS0 /\
                  pcredit_x L cr ps kx bx /\ obj_on_stack L sp P 272 /\ obj_on_stack L sp V 48 /\ obj_on_stack L sp E 16 /\
                  apart P 272 V 48 /\ apart P 272 E 16 /\ apart V 48 E 16)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code : Z) (g' : ls_state),
          PAout ps M' P ps' /\ PMCUR.wf_c ps' /\ win_ok M' LBo ps' /\ buf_bound ps' B /\ ec_at M' E code /\ (code <> 0 -> ps_more ps' = false) /\
          ls_ok g' M' /\ (g' = g \/ (g' = regJ g /\ code <> 0)) /\
          LB' = ps_blocks ps' ++ LBo /\ LBk = LBo /\ W = W_parc P V E /\ pcredit_x L cr' ps' kx bx /\ Rel ps ps' code R' /\ PMCUR.cur_post RSEGS ps ps' code M' V).

Definition ptrans_gbk (WFin : pstate -> Prop) (BBin : pstate -> Z -> Prop) (PAin : mem -> Z -> pstate -> Prop) (PAout : pstate -> mem -> Z -> pstate -> Prop)
           (pc scr : Z) (Args : bvmap 5 word -> mem -> Z -> Z -> Z -> pstate -> Prop)
           (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r P V E B kx bx : Z) (g : ls_state) (ps : pstate),
    cps_heap L HI pc r sp scr (ps_blocks ps ++ LBo) cr
      (fun R M => entry L R M sp r scr /\ Args R M P V E ps /\
                  PAin M P ps /\ WFin ps /\ win_ok M LBo ps /\ BBin ps B /\ vis_at M V /\ ec_at M E 0 /\ ls_ok g M /\ g <> LS0 /\
                  pcredit_x L cr ps kx bx /\ obj_on_stack L sp P 272 /\ obj_on_stack L sp V 48 /\ obj_on_stack L sp E 16 /\
                  apart P 272 V 48 /\ apart P 272 E 16 /\ apart V 48 E 16)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code : Z) (g' : ls_state),
          PAout ps M' P ps' /\ PMCUR.wf_c ps' /\ win_ok M' LBo ps' /\ buf_bound ps' B /\ ec_at M' E code /\ (code <> 0 -> ps_more ps' = false) /\
          ls_ok g' M' /\ (g' = g \/ (g' = regJ g /\ code <> 0)) /\
          LB' = ps_blocks ps' ++ LBo /\ LBk = LBo /\ W = W_par P E /\ pcredit_x L cr' ps' kx bx /\ Rel ps ps' code R').

Definition ptrans_g := ptrans_gb PMCUR.wf_c buf_bound.

Definition buf_bound_stale (ps : pstate) (B : Z) : Prop := Z.of_nat (length (ps_buf ps)) + winlen ps <= B /\ B < 2 ^ 26 /\ 0 <= winlen ps.

Definition ptrans := ptrans_g parser_at (fun _ => parser_at).

Definition ptrans_cur := ptrans_g parser_at (fun ps M' P ps' => parser_at M' P (ps_set_win ps' (ps_win ps))).

Definition ptrans_stale (pc scr : Z) (Args : bvmap 5 word -> mem -> Z -> Z -> Z -> pstate -> Prop) (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall mw : option (Z * Z),

    ptrans_gb PMCUR.wf_c_stale buf_bound_stale (fun M P ps => parser_at M P (ps_set_win ps mw)) (fun ps M' P ps' => parser_at M' P (ps_set_win ps' mw) /\ ps_win ps' = ps_win ps) pc scr Args Rel.

Definition ptrans_stalek (pc scr : Z) (Args : bvmap 5 word -> mem -> Z -> Z -> Z -> pstate -> Prop) (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall mw : option (Z * Z),
    ptrans_gbk PMCUR.wf_c_stale buf_bound_stale (fun M P ps => parser_at M P (ps_set_win ps mw)) (fun ps M' P ps' => parser_at M' P (ps_set_win ps' mw) /\ ps_win ps' = ps_win ps) pc scr Args Rel.

Definition no_args : bvmap 5 word -> mem -> Z -> Z -> Z -> pstate -> Prop := fun _ _ _ _ _ _ => True.
Definition std_args (R : bvmap 5 word) (M : mem) (P V E : Z) (ps : pstate) : Prop := a0 R P /\ a1 R V /\ a2 R E.
Definition cur_args (R : bvmap 5 word) (M : mem) (P V E : Z) (ps : pstate) : Prop :=
  a0 R P /\ a2 R V /\ a3 R E /\ exists p e, ps_win ps = Some (p, e) /\ a1 R p.
Definition win_exhausted (ps : pstate) : Prop := match ps_win ps with None => True | Some (p, e) => p = e end.
Definition consumed (ps ps' : pstate) : Prop :=
  match ps_win ps, ps_win ps' with Some (p, e), Some (p', e') => e' = e /\ p < p' <= e | _, _ => False end.
Definition not_retreated (ps ps' : pstate) : Prop :=
  match ps_win ps, ps_win ps' with Some (p, e), Some (p', e') => e' = e /\ p <= p' <= e | None, None => True | _, _ => False end.

Definition set_ec_spec : Prop :=
  forall (E code sp r : Z) (g : ls_state),
    cps_pure PC_SET_EC r sp SETEC_SCR [(E, 16); (0xd4df8, 2); (0xf6848, 544)]
      (fun R M => entry L R M sp r SETEC_SCR /\ a0 R E /\ a1 R code /\ 1 <= code <= 31 /\ L5.defined M E 16 /\ obj_on_stack L sp E 16 /\ ls_ok g M /\ g <> LS0)
      (fun R M R' M' => ec_at M' E code /\ ls_ok (regJ g) M' /\ a0 R' E).

Definition PC_CONV_EC : Z := 0x3a54c.
Definition ec_conv_at (M : mem) (E : Z) (code : Z) : Prop := u32 M E code /\ L5.defined M E 16 /\ u64 M (E + 8) OBJ_CONV_CATEGORY.
Definition conv_ec_spec : Prop :=
  forall (E code sp r : Z) (g : ls_state),
    cps_pure PC_CONV_EC r sp SETEC_SCR [(E, 16); (0xd4df0, 2); (0xf6848, 544)]
      (fun R M => entry L R M sp r SETEC_SCR /\ a0 R E /\ a1 R code /\ 1 <= code <= 31 /\ L5.defined M E 16 /\ obj_on_stack L sp E 16 /\ ls_ok g M /\ g <> LS0)
      (fun R M R' M' => ec_conv_at M' E code /\ ls_ok (regC g) M' /\ a0 R' E).

Definition pop_state_spec : Prop :=
  forall (P x sp r : Z) (ps : pstate) (rest : list Z),
    cps_pure PC_POP_STATE r sp 48 [(P + 256, 8)]
      (fun R M => entry L R M sp r 48 /\ a0 R P /\ parser_at M P ps /\ ps_stack ps = rest ++ [x] /\ obj_on_stack L sp P 272 /\

                  0 <= x < 256 /\ 4096 <= ps_sb ps /\ ps_sb ps + ps_scap ps <= hl_ceil L)
      (fun R M R' M' => a0 R' x /\ u64 M' (P + 256) (ps_sb ps + Z.of_nat (length rest))).
Definition parent_spec : Prop :=
  forall (P x sp r : Z) (ps : pstate) (rest : list Z),
    cps_pure PC_PARENT r sp 48 []
      (fun R M => entry L R M sp r 48 /\ a0 R P /\ parser_at M P ps /\ ps_stack ps = rest ++ [x] /\ obj_on_stack L sp P 272 /\
                  0 <= x < 256 /\ 4096 <= ps_sb ps /\ ps_sb ps + ps_scap ps <= hl_ceil L)
      (fun R M R' M' => a0 R' x).

Definition skip_space_spec : Prop :=
  ptrans PC_SKIP_SPACE PF_SCR (fun R M P V E ps => a0 R P /\ a1 R (P + 200) /\ ws_ok ps /\

                                                   ps_more ps = true /\ is_expect (ps_st ps) /\
                                                   exists p e b, ps_win ps = Some (p, e) /\ p < e /\ u8 M p b /\ In b [9; 10; 13; 32])
         (fun ps ps' code R' => code = 0 /\ consumed ps ps' /\ ps_more ps' = ps_more ps /\ ws_ok ps' /\
                                (ps_st ps' = ps_st ps \/ (ps_st ps' = ST_CR /\ win_exhausted ps')) /\ ps_level ps' = ps_level ps).

Definition begin_container_spec (pc kind st' : Z) : Prop :=
  ptrans pc PF_SCR (fun R M P V E ps => std_args R M P V E ps /\ ps_more ps = true /\ ~ comment_or_cr (ps_st ps) /\ ps_st ps <> ST_STRING)
         (fun ps ps' code R' =>
            (code = 0 /\ ps_level ps' = ps_level ps + 1 /\ ps_st ps' = st' /\ ps_more ps' = false /\ ps_stack ps' = ps_stack ps ++ [kind] /\ ps_win ps' = ps_win ps)
            \/ (code = 5 /\ ps_level ps = 1024)).
Definition begin_object_spec := begin_container_spec PC_BEGIN_OBJECT ST_OBJECT ST_EXPECT_MEMBER_NAME_OR_END.
Definition begin_array_spec := begin_container_spec PC_BEGIN_ARRAY ST_ARRAY ST_EXPECT_VALUE_OR_END.

Definition end_container_spec (pc kind : Z) : Prop :=
  ptrans pc PF_SCR (fun R M P V E ps => std_args R M P V E ps /\ ps_more ps = true /\ ~ comment_or_cr (ps_st ps) /\ ps_st ps <> ST_STRING)
         (fun ps ps' code R' =>
            (code = 0 /\ ps_level ps' = ps_level ps - 1 /\ ps_more ps' = false /\ (exists rest, ps_stack ps = rest ++ [kind] /\ ps_stack ps' = rest) /\
             ps_st ps' = (if Z.eqb (ps_level ps') 0 then ST_ACCEPT else ST_EXPECT_COMMA_OR_END) /\ ps_win ps' = ps_win ps)
            \/ In code [20; 21; 22; 23]).
Definition end_object_spec := end_container_spec PC_END_OBJECT ST_OBJECT.
Definition end_array_spec := end_container_spec PC_END_ARRAY ST_ARRAY.

Definition begin_member_spec : Prop :=
  ptrans PC_BEGIN_MEMBER PF_SCR (fun R M P V E ps => a0 R P /\ a1 R E /\ ps_more ps = true /\ ps_st ps = ST_EXPECT_COMMA_OR_END)
         (fun ps ps' code R' => code = 0 /\ ps_more ps' = true /\ In (ps_st ps') [ST_EXPECT_MEMBER_NAME; ST_EXPECT_VALUE] /\
                                ps_stack ps' = ps_stack ps /\ ps_level ps' = ps_level ps /\ ps_win ps' = ps_win ps).
Definition after_value_spec : Prop :=
  ptrans_stalek PC_AFTER_VALUE AFTERV_SCR (fun R M P V E ps => a0 R P /\ a1 R E /\ ps_more ps = false /\ ps_st ps = ST_NUMBER /\

                                                                   PMCUR.wf_c_stale (PMCUR.ps_set_more ps true))
         (fun ps ps' code R' => PMCUR.wf_c (PMCUR.ps_set_more ps' true) /\ code = 0 /\ ps_more ps' = false /\ ps_st ps' = (if Z.eqb (ps_level ps) 0 then ST_ACCEPT else ST_EXPECT_COMMA_OR_END) /\
                                ps_stack ps' = ps_stack ps /\ ps_level ps' = ps_level ps /\ ps_win ps' = ps_win ps /\

                                ps_bptr ps' = ps_bptr ps /\ length (ps_buf ps') = length (ps_buf ps)).

Definition literal_rel (ps ps' : pstate) (code : Z) : Prop :=
  (code = 0 /\ consumed ps ps' /\ ps_stack ps' = ps_stack ps /\ ps_level ps' = ps_level ps) \/ code = 11.

Definition parse_true_spec : Prop :=
  ptrans_cur PC_PARSE_TRUE PF_SCR (fun R M P V E ps => cur_args R M P V E ps /\ ps_more ps = true /\ ~ win_exhausted ps /\ is_expect (ps_st ps))
         (fun ps ps' code R' => literal_rel ps ps' code /\ not_retreated ps ps' /\ (exists p e, ps_win ps' = Some (p, e) /\ a0 R' p)).
Definition parse_false_spec : Prop :=
  ptrans_cur PC_PARSE_FALSE PF_SCR (fun R M P V E ps => cur_args R M P V E ps /\ ps_more ps = true /\ ~ win_exhausted ps /\ is_expect (ps_st ps))
         (fun ps ps' code R' => literal_rel ps ps' code /\ not_retreated ps ps' /\ (exists p e, ps_win ps' = Some (p, e) /\ a0 R' p)).
Definition parse_null_spec : Prop :=
  ptrans PC_PARSE_NULL PF_SCR (fun R M P V E ps => std_args R M P V E ps /\ ps_more ps = true /\ ~ win_exhausted ps /\ is_expect (ps_st ps))
         (fun ps ps' code R' => literal_rel ps ps' code).

Definition validate_spec : Prop :=
  forall (s len sp r : Z),
    cps_pure PC_VALIDATE r sp 96 []
      (fun R M => entry L R M sp r 96 /\ a0 R s /\ a1 R len /\ 0 <= len < 2 ^ 27 /\ L5.defined M s len /\ img_ro M /\
                  4096 <= s /\ s + len <= hl_ceil L)
      (fun R M R' M' => exists q c, a0 R' q /\ getr R' 11%bv = Z_to_bv 64 c /\ s <= q <= s + len /\ 0 <= c <= 6).

Definition end_string_value_spec : Prop :=
  ptrans_stale PC_END_STRING ESV_SCR
         (fun R M P V E ps => a0 R P /\ a3 R V /\ getr R 14%bv = Z_to_bv 64 E /\ ps_more ps = true /\ ps_st ps = ST_STRING /\
                              exists s len, a1 R s /\ a2 R len /\ 0 <= len < 2 ^ 26 /\ L5.defined M s len /\
                                            4096 <= s /\ s + len <= hl_ceil L /\
                                            PMCUR.txt_ok (ps_win ps) ps s len)
         (fun ps ps' code R' =>
            (code = 0 /\ ps_more ps' = false /\ ps_level ps' = ps_level ps /\
             In (ps_st ps') [ST_EXPECT_COLON; ST_EXPECT_COMMA_OR_END; ST_ACCEPT])
            \/ In code [25; 26; 27; 28; 29]).

Definition parse_string_spec : Prop :=
  ptrans_cur PC_PARSE_STRING PF_SCR (fun R M P V E ps => cur_args R M P V E ps /\ ps_more ps = true /\ ps_st ps = ST_STRING)
         (fun ps ps' code R' => not_retreated ps ps' /\ (exists p e, ps_win ps' = Some (p, e) /\ a0 R' p) /\
                                (code <> 0 \/ consumed ps ps' \/ win_exhausted ps) /\

                                (code = 0 -> ps_level ps' = ps_level ps)).

Definition dec_u64_spec : Prop :=
  forall (s len vp sp r : Z),
    cps_pure PC_DEC_U64 r sp 16 [(vp, 8)]
      (fun R M => entry L R M sp r 16 /\ a0 R s /\ a1 R len /\ a2 R vp /\ 0 <= len < 2 ^ 27 /\ L5.defined M s len /\ L5.defined M vp 8 /\ sp <= vp /\ vp + 8 <= hl_sptop L /\ img_ro M /\ 4096 <= s /\ s + len <= hl_ceil L  )
      (fun R M R' M' => exists q c, a0 R' q /\ getr R' 11%bv = Z_to_bv 64 c /\ In c [0; 22; 34]).

Definition decstr_to_double_spec : Prop :=
  forall (s dp sp r : Z) (txt : list Z),
    cps_pure PC_DECSTR_DOUBLE r sp (96 + STRTOD_SCR) [(dp, 8); (TP - 164, 4)]
      (fun R M => entry L R M sp r (96 + STRTOD_SCR) /\ a0 R s /\ a1 R (Z.of_nat (length txt)) /\ a2 R dp /\ img_ro M /\
                  L5.bytes_at RSEGS M s txt /\ u8 M (s + Z.of_nat (length txt)) 0 /\ num_final txt /\ Z.of_nat (length txt) < 2 ^ 26 /\
                  L5.defined M dp 8 /\ sp <= dp /\ dp + 8 <= hl_sptop L /\

                  L5.defined M s (Z.of_nat (length txt) + 1) /\ 4096 <= s /\ s + Z.of_nat (length txt) < 2 ^ 47 /\
                  (s + Z.of_nat (length txt) + 1 <= sp - (96 + STRTOD_SCR) \/ sp <= s) /\
                  (s + Z.of_nat (length txt) + 1 <= TP - 164 \/ TP - 160 <= s))
      (fun R M R' M' => a0 R' (s + Z.of_nat (length txt)) /\ exists c, getr R' 11%bv = Z_to_bv 64 c /\ In c [0; 34]).

Definition end_number_spec (pc : Z) : Prop :=
  ptrans_stale pc ENDNUM_SCR (fun R M P V E ps => std_args R M P V E ps /\ ps_more ps = true /\ ps_st ps = ST_NUMBER /\ num_final (ps_buf ps))
         (fun ps ps' code R' => (code = 0 /\ ps_more ps' = false /\ ps_st ps' = (if Z.eqb (ps_level ps) 0 then ST_ACCEPT else ST_EXPECT_COMMA_OR_END) /\
                                 ps_stack ps' = ps_stack ps /\ ps_level ps' = ps_level ps /\ ps_win ps' = ps_win ps) \/ code = 19).
Definition end_integer_value_spec := end_number_spec PC_END_INT.
Definition end_fraction_value_spec := end_number_spec PC_END_FRAC.

Definition parse_number_spec : Prop :=
  ptrans_cur PC_PARSE_NUMBER PF_SCR (fun R M P V E ps => cur_args R M P V E ps /\ ps_more ps = true /\ ps_st ps = ST_NUMBER)
         (fun ps ps' code R' => not_retreated ps ps' /\ (exists p e, ps_win ps' = Some (p, e) /\ a0 R' p) /\

                                (code = 0 -> ps_level ps' = ps_level ps /\ (ps_st ps' = ST_NUMBER -> win_exhausted ps') /\
                                             In (ps_st ps') [ST_NUMBER; ST_ACCEPT; ST_EXPECT_COMMA_OR_END])).

Definition parse_some_spec : Prop :=

  ptrans PC_PARSE_SOME PSOME_SCR (fun R M P V E ps => std_args R M P V E ps /\ ps_more ps = true)
         (fun ps ps' code R' =>
            (code <> 0 \/ ps_more ps' = false \/ win_exhausted ps') /\
            (ps_st ps = ST_ACCEPT -> code = 0 /\ ps_more ps' = false /\ ps_done ps' = true) /\

            (win_exhausted ps -> code = 0 -> ps_more ps' = true -> In (ps_st ps) [ST_NUMBER; ST_CR] /\ ~ In (ps_st ps') [ST_NUMBER; ST_CR])).

Definition skip_whitespace_spec : Prop :=

  ptrans PC_SKIP_WS SKIPWS_SCR (fun R M P V E ps => a0 R P /\ ws_ok ps /\ (ps_more ps = true -> win_exhausted ps))
         (fun ps ps' code R' => code = 0 /\ not_retreated ps ps' /\ ps_more ps' = ps_more ps /\ ws_ok ps').
Definition parser_check_done_spec : Prop :=
  ptrans PC_PCHECK_DONE PF_SCR (fun R M P V E ps => a0 R P /\ a1 R E)

         (fun ps ps' code R' => (code = 0 /\ win_exhausted ps' /\ ps_more ps' = ps_more ps /\ ps_st ps' = ps_st ps /\ ps_stack ps' = ps_stack ps /\ ps_level ps' = ps_level ps) \/ code = 4).

Definition reader_pre (M : mem) (LBo : list (Z * Z)) (Rr IS V E ch : Z) (rep : srep) (gp rdst : Z) (bof : bool) (ps : pstate) (sp : Z) : Prop :=
  reader_at M Rr IS V ch bof ps /\ wf_ps ps /\ isrc_at M IS rep gp rdst /\ vis_at M V /\ ec_at M E 0 /\
  In (ch, 16384) LBo /\ (forall b, In b (srep_blocks rep) -> In b LBo) /\
  obj_on_stack L sp Rr 592 /\ obj_on_stack L sp IS 272 /\ obj_on_stack L sp V 8 /\ obj_on_stack L sp E 16 /\
  apart Rr 592 IS 272 /\ apart Rr 592 V 8 /\ apart Rr 592 E 16 /\ apart IS 272 V 8 /\ apart IS 272 E 16 /\ apart V 8 E 16.

Definition ps_init (sb bptr : Z) : pstate := PS ST_START 0 0 true false 0 [ST_ROOT] sb 66 264 bptr [] None.

Definition read_spec : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r Rr IS V E ch gp sb bptr kx bx : Z) (rep : srep) (g : ls_state),
    let ps := ps_init sb bptr in
    cps_heap L HI PC_READ r sp READ_SCR (ps_blocks ps ++ LBo) cr
      (fun R M => entry L R M sp r READ_SCR /\ a0 R Rr /\ a1 R E /\
                  reader_pre M LBo Rr IS V E ch rep gp 0 true ps sp /\ gp = srep_data (IS + 80) rep /\
                  (forall b, In b (srep_blocks rep) -> fst b <> ch) /\
                  Z.of_nat (length (srep_chars rep)) < 2 ^ 26 /\ ls_ok g M /\ g <> LS0 /\ pcredit_x L cr ps kx bx)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code gp' rdst' : Z) (g' : ls_state),

          source_at M' Rr ch /\ parser_at M' (Rr + 320) ps' /\ isrc_at M' IS rep gp' rdst' /\ ec_at M' E code /\
          ls_ok g' M' /\ (g' = g \/ (g' = regJ g /\ code <> 0)) /\
          LB' = ps_blocks ps' ++ LBo /\ LBk = lb_remove ch LBo /\ pcredit_x L cr' ps' kx bx /\ wf_ps ps' /\
          W = [(Rr, 592); (IS, 272); (E, 16); (0xd4df8, 2); (0xf6848, 544)]).

Definition gloc_done (M : mem) : Prop := u8 M 0xd5230 1 /\ u64 M 0xd5228 CLASSIC_IMP.

Definition locale_ctor_later_spec : Prop :=
  forall (o sp r : Z),
    cps_pure PC_LOCALE_CTOR r sp 32 [(o, 8)]
      (fun R M => entry L R M sp r 32 /\ a0 R o /\ gloc_done M /\ img_ro M /\ obj_on_stack L sp o 8 /\ L5.defined M o 8)
      (fun R M R' M' => u64 M' o CLASSIC_IMP).

Definition locale_ctor_first_spec : Prop :=
  forall (o sp r : Z),
    cps_pure PC_LOCALE_CTOR r sp ISLAND_SCR ((o, 8) :: map (fun iv => (fst iv, snd iv - fst iv)) ll_prist_csrc  )
      (fun R M => entry L R M sp r ISLAND_SCR /\ a0 R o /\ ls_ok LS0 M /\ obj_on_stack L sp o 8 /\ L5.defined M o 8)
      (fun R M R' M' => u64 M' o CLASSIC_IMP /\ u8 M' 0xd5230 1 /\ u64 M' 0xd5228 CLASSIC_IMP /\ errcat_guard M' 0 /\ convcat_guard M' 0 /\ atexit_cells M' [] /\
                        u8 M' 0xd5030 0 /\ u8 M' 0xd5031 0 /\ libc_quiet M'  ).

Definition locale_dtor_spec : Prop :=
  forall (o sp r : Z),
    cps_pure PC_LOCALE_DTOR r sp 0 []
      (fun R M => entry L R M sp r 0 /\ a0 R o /\ 0 <= o < 2 ^ 62   /\ u64 M o CLASSIC_IMP)
      (fun R M R' M' => True).

Definition strinit_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (o src sp r : Z) (txt : list Z),
    cps_heap L HI PC_STRINIT r sp (48 + OPNEW_SCR) LB cr
      (fun R M => entry L R M sp r (48 + OPNEW_SCR) /\ a0 R o /\ a1 R src /\ a2 R (Z.of_nat (length txt)) /\ Z.of_nat (length txt) < 2 ^ 26 /\
                  L5.bytes_at RSEGS M src txt /\ L5.defined M src (Z.of_nat (length txt)) /\ obj_on_stack L sp o 24 /\ L5.defined M o 24 /\
                  (txt = [] \/ exists b, In b LB /\ fst b <= src /\ src + Z.of_nat (length txt) <= fst b + snd b) /\
                  ((23 <= length txt)%nat -> credit_ok L cr (str_cap (Z.of_nat (length txt)))))
      (fun R M R' M' LB' cr' LBk W => W = [(o, 24)] /\ LBk = LB /\
          (((length txt <= 22)%nat /\ str_at_w M' o (SShort txt) /\ LB' = LB /\ cr' = cr)
        \/ ((23 <= length txt)%nat /\ exists p, let cap := str_cap (Z.of_nat (length txt)) in
             str_at_w M' o (SLong cap p txt)   /\ L5C.fresh_block L LB M' p cap /\ LB' = (p, cap) :: LB /\ cr' = debit L cr cap))).

Definition statics_mid (M : mem) : Prop :=
  img_ro M /\ libc_quiet M   /\ gloc_done M /\ ((u8 M 0xd5030 0 /\ u8 M 0xd5031 0) \/ u8 M 0xd5030 1) /\
  (exists g, g <> LS0 /\ errcat_guard M (jbit g) /\ convcat_guard M (cbit g) /\ atexit_cells M (ls_atexit g)).

Definition iss_ctor_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (IS so sp r : Z) (srep0 : srep),
    cps_heap L HI PC_ISS_CTOR r sp (80 + Z.max CTOR_SCR ISLAND_SCR) LB cr
      (fun R M => entry L R M sp r (80 + Z.max CTOR_SCR ISLAND_SCR) /\ a0 R IS /\ a1 R so /\ a2 R 8 /\
                  str_at_w M so srep0   /\ (forall b, In b (srep_blocks srep0) -> In b LB) /\ Z.of_nat (length (srep_chars srep0)) < 2 ^ 26 /\
                  obj_on_stack L sp IS 272 /\ obj_on_stack L sp so 24 /\ apart IS 272 so 24 /\ L5.defined M IS 272 /\
                  L5.defined M so 24   /\
                  (ls_ok LS0 M \/ statics_mid M) /\
                  credit_ok L cr (copy_cap (Z.of_nat (length (srep_chars srep0)))))
      (fun R M R' M' LB' cr' LBk W => exists rep,
          srep_chars rep = srep_chars srep0 /\ isrc_at M' IS rep (srep_data (IS + 80) rep) 0 /\ statics_mid M' /\
          LB' = srep_blocks rep ++ LB /\ LBk = LB /\
          (forall b, In b (srep_blocks rep) -> L5C.fresh_block L LB M' (fst b) (snd b) /\ snd b = copy_cap (Z.of_nat (length (srep_chars srep0))) /\ cr' = debit L cr (snd b)) /\
          (srep_blocks rep = [] -> cr' = cr) /\
          W = (IS, 272) :: map (fun iv => (fst iv, snd iv - fst iv)) ll_foot_csrc).

Definition reader_ctor_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (Rr IS V sp r : Z),
    cps_heap L HI PC_READER_CTOR r sp (304 + CTOR_SCR) LB cr
      (fun R M => entry L R M sp r (304 + CTOR_SCR) /\ a0 R Rr /\ a1 R IS /\ a2 R V /\
                  (exists rep gp, isrc_at M IS rep gp 0) /\ vis_at M V /\ img_ro M /\ gloc_done M /\
                  obj_on_stack L sp Rr 592 /\ obj_on_stack L sp IS 272 /\ obj_on_stack L sp V 8 /\ apart Rr 592 IS 272 /\ apart Rr 592 V 8 /\ L5.defined M Rr 592 /\
                  3 * hl_k_per_malloc L <= fst cr /\ 16384 + 264 + 66 + 3 * hl_b_overhead L <= snd cr)
      (fun R M R' M' LB' cr' LBk W => exists ch sb bptr,
          reader_at M' Rr IS V ch true (ps_init sb bptr) /\
          LB' = ps_blocks (ps_init sb bptr) ++ (ch, 16384) :: LB /\ LBk = LB /\ W = [(Rr, 592)] /\
          cr' = debit L (debit L (debit L cr 16384) 264) 66).

Definition source_dtor_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (Rr ch sp r : Z),
    cps_heap L HI PC_SOURCE_DTOR r sp (96 + OPDEL_SCR) LB cr
      (fun R M => entry L R M sp r (96 + OPDEL_SCR) /\ a0 R Rr /\ source_at M Rr ch   /\ In (ch, 16384) LB /\ img_ro M /\ obj_on_stack L sp Rr 592)
      (fun R M R' M' LB' cr' LBk W => LB' = lb_remove ch LB /\ cr' = cr /\ LBk = lb_remove ch LB /\ W = [(Rr, 592)]).

Definition parser_dtor_spec : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r P : Z) (ps : pstate),
    cps_heap L HI PC_PARSER_DTOR r sp (64 + OPDEL_SCR) (ps_blocks ps ++ LBo) cr
      (fun R M => entry L R M sp r (64 + OPDEL_SCR) /\ a0 R P /\ parser_at M P ps /\ img_ro M /\ obj_on_stack L sp P 272 /\ 0 < ps_scap ps <= 4096)
      (fun R M R' M' LB' cr' LBk W => LB' = LBo /\ cr' = cr /\ LBk = LBo /\ W = [(P, 272)]).

Definition pm_statics : lib_statics := {| LibIface.ls_state := PML.ls_state; LibIface.ls_ok := PML.ls_ok; LibIface.ls_g0 := LS0 |}.
Definition pm_credit (n : Z) : credit := (28 * hl_k_per_malloc L, 2 * n + 2 ^ 28 + 32768 + 28 * hl_b_overhead L).
Definition pm_layout_ok (Lay : lib_layout) : Prop :=
  ll_heap Lay = L /\ ll_entry Lay = PC_LIB /\ ll_gp Lay = 0x10800 /\ LIB_SCR <= ll_stack Lay   /\ ll_foot Lay = ll_foot_csrc /\
  (forall n, ll_credit Lay n = pm_credit n) /\ IMG_RO_HI <= ll_rw_lo Lay.

Definition lib_call_ok_fp (Lay : lib_layout) (LSt : lib_statics) : Prop :=
  forall (fx : FPState) (g : LibIface.ls_state LSt) (LB : list (Z * Z)) (cr : credit) (sp ptr ra : Z) (payload : list byte)
         (R : bvmap 5 word) (M : mem) (model : Model) (K : ShapeAlg.TSet),
    fp_ok fx ->
    lib_pre Lay LSt g LB cr sp ptr ra payload R M ->
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    K [] ->
    (forall (fx' : FPState) (g' : LibIface.ls_state LSt) (R' : bvmap 5 word) (M' : mem) (model' : Model) (cr' : credit),
        fp_ok fx' ->
        lib_post Lay LSt g' LB cr sp payload R M R' M' cr' ->
        hi_heap HI LB cr' M' (m_vmmaps model') ->
        model_but_vm model model' ->
        srealizes (hl_segs (ll_heap Lay)) SCFG (@lib_cfg Lay fx' R' (Z_to_bv 64 ra) M' model') K) ->
    srealizes (hl_segs (ll_heap Lay)) SCFG (@lib_cfg Lay fx R (Z_to_bv 64 (ll_entry Lay)) M model) K.
Definition lib_spec (Lay : lib_layout) : Prop := pm_layout_ok Lay -> lib_call_ok_fp Lay pm_statics.

Definition VIS_SCR : Z := 64.
Definition visit_spec (pc : Z) (Args : bvmap 5 word -> mem -> Prop) (Ev : bvmap 5 word -> mem -> PMCUR.sevent -> Prop) : Prop :=
  forall (V sp r : Z),
    cps_pure pc r sp VIS_SCR [(V + 8, 40)]
      (fun R M => entry L R M sp r VIS_SCR /\ a0 R V /\ vis_at M V /\ obj_on_stack L sp V 48 /\ Args R M)
      (fun R M R' M' => a0 R' 1 /\ exists e, Ev R M e /\ PMCUR.ev_at RSEGS M' V e).
Definition visit_const_spec (pc : Z) (e0 : PMCUR.sevent) : Prop := visit_spec pc (fun _ _ => True) (fun _ _ e => e = e0).
Definition visit_null_spec (pc : Z) : Prop := visit_const_spec pc PMCUR.EvNull.
Definition visit_begin_object_spec (pc : Z) : Prop := visit_const_spec pc PMCUR.EvBeginObj.
Definition visit_end_object_spec (pc : Z) : Prop := visit_const_spec pc PMCUR.EvEndObj.
Definition visit_begin_array_spec (pc : Z) : Prop := visit_const_spec pc PMCUR.EvBeginArr.
Definition visit_end_array_spec (pc : Z) : Prop := visit_const_spec pc PMCUR.EvEndArr.
Definition visit_bool_spec (pc : Z) : Prop := visit_spec pc (fun R _ => exists x, a1 R x /\ 0 <= x <= 1) (fun R _ e => exists x, a1 R x /\ 0 <= x <= 1 /\ e = PMCUR.EvBool (Z.eqb x 1)).
Definition visit_u64_spec (pc : Z) : Prop := visit_spec pc (fun _ _ => True) (fun R _ e => exists x, a1 R x /\ e = PMCUR.EvU64 x).
Definition visit_i64_spec (pc : Z) : Prop := visit_spec pc (fun _ _ => True) (fun R _ e => exists x, a1 R x /\ e = PMCUR.EvI64 x).
Definition visit_double_spec (pc : Z) : Prop := visit_spec pc (fun _ _ => True) (fun _ _ e => exists x, e = PMCUR.EvDbl x).
Definition visit_text_spec (pc : Z) (mk : Z -> Z -> PMCUR.sevent) : Prop :=
  visit_spec pc (fun R M => exists sv p n, a1 R sv /\ u64 M sv p /\ u64 M (sv + 8) n /\ 2 ^ 12 <= sv /\ sv + 16 <= 2 ^ 47)
             (fun R M e => exists sv p n, a1 R sv /\ u64 M sv p /\ u64 M (sv + 8) n /\ e = mk p n).
Definition visit_string_spec (pc : Z) : Prop := visit_text_spec pc PMCUR.EvStr.
Definition visit_key_spec (pc : Z) : Prop := visit_text_spec pc PMCUR.EvKey.

Definition PC_VIS_BEGIN_ARRAY_TAG : Z := 0x41e48.  Definition PC_VIS_END_ARRAY : Z := 0x41c6c.  Definition PC_VIS_U64 : Z := 0x41cc0.  Definition PC_VIS_I64 : Z := 0x41ce4.
Definition PC_VIS_DOUBLE : Z := 0x41d08.  Definition PC_VIS_FLUSH : Z := 0x41d2c.  Definition PC_VIS_BEGIN_OBJECT_TAG : Z := 0x41d30.  Definition PC_VIS_END_OBJECT : Z := 0x41df8.
Definition PC_VIS_KEY : Z := 0x41ea4.  Definition PC_VIS_NULL : Z := 0x41ed4.  Definition PC_VIS_BOOL : Z := 0x41f30.  Definition PC_VIS_STRING : Z := 0x41f54.
Definition atexit_handler_spec : Prop :=
  forall (sp r a : Z),
    cps_pure ATEXIT_HANDLER r sp 0 [] (fun R M => entry L R M sp r 0 /\ a0 R a) (fun R M R' M' => True).

End Specs.
End PMS.
