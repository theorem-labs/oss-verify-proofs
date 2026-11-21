(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (time() reaches the vDSO: the pre-revision walks through a NULL __vdsosym and the clock_gettime trap, vdsosym_spec, cgt_init_spec, atime_front and atime_back with au64s_read, are removed; acgt_init_v, atime_front_v and atime_back_v walk cgt_init, ASan's time interceptor, time and clock_gettime to and from the vDSO entry over the run's segment list, the __vdsosym call taken by As/AVdsoWalk.v). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Decode Exec CellsX TacX VdsoImg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import STRW_tac.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsShadow AsConst AsIface ECH_AImg F_time AsAuxv.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import N6_rip N6_strlen F_strspn.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import AsStrcmp AVdsoAddr AVdsoSegs AVdsoSym AVdsoWalk.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import InNth.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* As/AsStrcmp.v's guard: the load and store solvers accept a cell only at a small non-negative
   offset from its base, so a far-away literal cell is refused at once instead of being unfolded
   into a unary offset. *)
Local Ltac asc_nonneg_lit d := lazymatch (eval vm_compute in (andb (Z.leb 0 d) (Z.leb d 4096))) with true => d end.
Local Ltac addr_diff E A ::=
  lazymatch E with
  | Z.add ?X ?c1 =>
      lazymatch A with
      | Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in let d := eval vm_compute in (c1 - c2)%Z in asc_nonneg_lit d
      | X => let c1 := zlit c1 in asc_nonneg_lit c1
      | _ => let e := zlit E in let a := zlit A in let d := eval vm_compute in (e - a)%Z in asc_nonneg_lit d
      end
  | _ =>
      lazymatch A with
      | Z.add E ?c2 => let c2 := zlit c2 in let d := eval vm_compute in (- c2)%Z in asc_nonneg_lit d
      | E => constr:(0%Z)
      | _ => let e := zlit E in let a := zlit A in let d := eval vm_compute in (e - a)%Z in asc_nonneg_lit d
      end
  end.

(* WHAT IS PROVED, over the run's segment list [asegs ++ tail] (the binary's segments followed by
   the vDSO pair), at LPS 727298f3 where the auxv publishes the vDSO and time() reads the clock
   there.  The model's vDSO call itself (Spec/VdNode.v) sits between the front and the back and
   is the caller's (As/F_timeI.v).
   1. [acgt_init_v]: musl's cgt_init (P_cgt_init) calls __vdsosym (As/AVdsoWalk.v
      [avdsosym_walk], which returns the vDSO's clock_gettime entry vb + 1460 = hvdso), stores it
      into vdso_func by its lr/sc loop, pops its 32-byte frame and jumps there.
   2. [atime_front_v]: from P_time, the [j] slot in front of ASan's time interceptor; the
      interceptor's prologue (0x7f0 + 0x70 = 2144 bytes) and its init-once test (16 bytes, a
      sibling call); REAL(time) read from ATIMEP_CELL, i.e. musl's time (48 bytes) with
      [*t] = the interceptor's local at sp - 80; clock_gettime (32 bytes) loading vdso_func and
      calling it.  vdso_func holds hvdso or P_cgt_init; in the second case cgt_init runs first
      (1.).  Either way the machine stands at hvdso with clock_gettime's return address in ra.
   3. [atime_back_v]: from clock_gettime's return of 0 back through time (which stores tv_sec at
      the interceptor's local and checks the canary) and the interceptor (t = NULL, so straight to
      its epilogue) to the caller's ra.
   Facts the caller holds over [asegs] reach [asegs ++ tail] by Common/Cfg/RunTailLazy.v's
   [lzt_*_keep] lemmas and come back off the vDSO window by its [lzt_*_back] lemmas. *)

(* ---- THE ADDRESS BLOCK (echconfiglist_parser.asan), read from the disassembly ---- *)
Definition ATW_INIT_RET : Z := 0x1b13c4.  (* jal 0x1a6c0 at 0x1b13c0 (the init-once test 0x1cba80) *)
Definition ATW_PAT_CELL : Z := 0x10618.   (* auipc a0,0xffe5f; ld s4,0x250(a0) at 0x1b13c8 *)
Definition ATW_ICPT_RET : Z := 0x1b13e4.  (* jalr a1 at 0x1b13e0: REAL(time) = 0x537568 *)
Definition ATW_TIME_RET : Z := 0x537598.  (* jal -0x2760 at 0x537594: clock_gettime 0x534e34 *)
Definition ATW_CG_RET   : Z := 0x534e64.  (* jalr a2 at 0x534e60: the vdso_func entry *)
Definition ATW_CGI_RET  : Z := 0x534f18.  (* jal 0x60 at 0x534f14 in cgt_init: __vdsosym 0x534f74 *)
(* --------------------------------------------------------------------------------- *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma amo_aligned_Z : forall wd z, 0 <= z < 2^64 -> z mod amo_bytes wd = 0 -> amo_aligned wd (Z_to_bv 64 z) = true.
Proof. intros wd z Hz Hm. unfold amo_aligned. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.
Ltac amo_fix :=
  repeat match goal with
  | |- context [amo_aligned ?wd (Z_to_bv 64 ?z)] =>
      rewrite (amo_aligned_Z wd z) by (first [cbn [amo_bytes]; lia | cbn [amo_bytes]; nia]); cbn [negb]
  end;
  repeat match goal with
  | |- context [Z.eqb ?x ?x] => rewrite (Z.eqb_refl x)
  end;
  cbv beta iota delta [amo_val inval_resv with_resv c_resv].
Ltac astep_core segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          amo_fix; simp_regs;
          try solve_load; try solve_store; reflexivity
        | simp_regs; vnorm_for i; mem_after_store_opt; post_step i ]
      | None => fail "undecodable instruction at" pc
      end
  | None => fail "no instruction at" pc
  end.
Ltac astep :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => astep_core segs R F pc fc rv m ro
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

(* the vDSO text base is page-aligned, so its clock_gettime entry is even (Ref/F_timeRun.v) *)
Lemma ats_even_entry : forall vb h : Z, vb mod 4096 = 0 -> vb + 1460 = h -> h mod 2 = 0.
Proof.
  intros vb h H E. subst h.
  rewrite (Z.div_mod vb 4096) by lia. rewrite H.
  replace (4096 * (vb / 4096) + 0 + 1460) with ((2048 * (vb / 4096) + 730) * 2) by lia.
  first [apply Z_mod_mult | apply Z.mod_mul; lia].
Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ATS : Z := 2192.   (* [comment removed for export] *)
Definition APAT : Z := 0xaaaaaaaaaaaaaaaa.   (* [comment removed for export] *)

  Variable tail : list Segment.

  Local Notation VS := (asegs ++ tail).

  (* a branch on a register holding [hvdso] against x0 *)
  Local Ltac if_false_nz :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with false;
        [ cbv iota
        | symmetry; unfold bv_eqb; rewrite ?w0_lit; rewrite ?unsigned_lit by lia; apply Z.eqb_neq; lia ]
    end.

  (* the target of a [jalr] through a register holding [hvdso], which is even *)
  Local Ltac fix_pc_hv HEV :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ ?pcx _ _ _ _) =>
        replace pcx with (Z_to_bv 64 hvdso)
          by first [ reflexivity
                   | symmetry; rewrite ?Z.add_0_r, ?ret_pc_fold; apply ret_pc_even; [lia | exact HEV] ]
    end.

  (* a callee's literal return address *)
  Local Ltac fix_ret_lit :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k)
          by (symmetry; apply ret_pc_even; [lia | reflexivity])
    | _ => idtac
    end.

  (* the caller's facts across a call whose footprint is [MUc]'s *)
  Local Ltac aw_transport mo mN MUc WMc :=
    let W := lazymatch type of MUc with munch ?W _ _ => W end in
    repeat match goal with
    | H : rw_cells (asegs ++ tail) mo ?A2 ?cs2 |- _ =>
        apply (rw_cells_transport (asegs ++ tail) W mo mN A2 cs2) in H;
        [ | exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia ]
    | H : ro_cells (asegs ++ tail) mo ?A2 ?cs2 |- _ =>
        apply (ro_cells_transport (asegs ++ tail) W mo mN A2 cs2) in H;
        [ | exact MUc | cbn [disjoint_from cells_size csize Nat.add]; lia ]
    | H : munch ?Wq ?mq mo |- _ =>
        apply (munch_trans Wq mq mo mN) in H;
        [ | apply (munch_weaken W Wq mo mN);
            [ unfold sub_fp; intros xq Hxq; cbn [outside] in Hxq |- *; repeat split; lia
            | exact MUc ] ]
    | H : wmono (asegs ++ tail) ?mq mo |- _ =>
        apply (wmono_trans (asegs ++ tail) mq mo mN) in H; [ | exact WMc ]
    end.

  (* -------- cgt_init: __vdsosym, the CAS, the tail call -------- *)

  (* 2352 = cgt_init's 32 bytes + __vdsosym's 2320 (AVdsoSym.AVW_FRAME) *)
  Definition acgt_init_post_v (ra sp gp tp a0 a1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 hvdso) fc None m' (seg_rom VS)
      /\ munch [(bv_unsigned sp - 2352, bv_unsigned sp); (A_vdso_func, A_vdso_func + 8)]%Z m m'
      /\ wmono VS m m' /\ mem_inv VS m'
      /\ stk VS m' lo (bv_unsigned sp) /\ rw_cells VS m' A_vdso_func [C8 (Z_to_bv 64 hvdso)].

  (* cgt_init at P_cgt_init: the vdso_func cell holds cgt_init itself; the auxv cell holds [av],
     whose pair 0 is (33, vb); the interceptor's facts are those of [avdsosym_walk]. *)
  Lemma acgt_init_v : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo av vb : Z),
    ro_cells VS m AAUXV_CELL [C8 (Z_to_bv 64 av)] ->
    ro_cells VS m av [C8 (Z_to_bv 64 33); C8 (Z_to_bv 64 vb)] ->
    rvdso_rom VS vb -> 0 < vb -> vb + 1460 = hvdso -> bv_unsigned sp <= av ->
    rw_cells VS m A_vdso_func [C8 (Z_to_bv 64 P_cgt_init)] ->
    stk VS m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 2352 -> mem_inv VS m ->
    vb + RVDSO_SPAN <= lo -> astrcmp_cells tail m ->
    astrcmp_shz tail m VW_NAME 20 -> astrcmp_shz tail m VW_VERNAME 10 ->
    astrcmp_shz tail m (vb + AVW_STRTAB) (AVW_STRSZ - 1) ->
    evt VS (acgt_init_post_v ra sp gp tp a0 a1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_cgt_init) fc None m (seg_rom VS)).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m lo av vb CELL AUXP ROMv VBP HVBv SPA VF ST CEIL LO MI VBLO CELLS SZN SZV SZT.
    acb.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof ROMv as (VB0 & VBA & VBH & _). rewrite RVDSO_SPAN_val in VBH.
    pose proof (ats_even_entry vb hvdso VBA HVBv) as HEV.
    pose proof (munch_refl [(bv_unsigned sp - 2352, bv_unsigned sp); (A_vdso_func, A_vdso_func + 8)]%Z m) as MU.
    pose proof (munch_refl [(bv_unsigned sp - 2352, bv_unsigned sp)]%Z m) as MUs.
    pose proof (wmono_refl (asegs ++ tail) m) as WM.
    (* the auxv cell's address as a literal, so the frame carving below keeps [CELL] *)
    unfold A_vdso_func, P_cgt_init, AAUXV_CELL in *.
    (* addi sp,sp,-32; sd ra,s0,s1; mv s0,a1; mv s1,a0; the two strings *)
    step. carve_frame 32%nat ST. do 9 step.
    (* jal __vdsosym *)
    step.
    eapply evt_cut.
    { eapply (avdsosym_walk tail) with (lo := lo) (av := av) (vb := vb).
      all: rewrite ?unsigned_lit by lia.
      all: first
        [ lazymatch goal with |- _ + RVDSO_SPAN <= _ => exact VBLO end
        | eassumption
        | (eapply av_cells_frame; [exact CELLS | exact MUs | unfold AIMG_TOP; lia])
        | (eapply av_shz_frame; [exact SZN | exact MUs | unfold AHI_LO; lia])
        | (eapply av_shz_frame; [exact SZV | exact MUs | unfold AHI_LO; lia])
        | (eapply av_shz_frame; [exact SZT | exact MUs | unfold AHI_LO; lia])
        | (unfold VW_AUXV_CELL; lia)
        | (unfold VW_AUXV_CELL; eapply ro_cells_transport; [exact CELL | exact MUs | cbn [disjoint_from cells_size csize Nat.add]; lia])
        | lia ]. }
    intros ms1 PV. unfold avdsosym_post_v in PV.
    destruct PV as (u0 & u1 & u2 & r0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & u3 & u4 & u5 & u6 & m1
                    & -> & E0 & MU1 & WM1 & MI1 & ST1).
    rewrite unsigned_lit in MU1, ST1 by lia.
    unfold RVDSO_CGT_OFF in E0. rewrite HVBv in E0. subst r0.
    fix_ret_lit.
    clear MUs CELL AUXP.
    lazymatch type of MU1 with munch _ ?m0 _ => aw_transport m0 m1 MU1 WM1 end.
    clear MU1 WM1. clear ST MI. rename ST1 into ST. rename MI1 into MI.
    (* mv t1,a0; a0 = &vdso_func; a1 = cgt_init *)
    step. step. step. step. step.
    (* lr.d; bne; sc.d; bnez: the CAS stores hvdso *)
    astep. step. if_false. astep. step. if_false.
    (* beqz t1: the entry is not null *)
    step. if_false_nz.
    (* mv a0,s1; mv a1,s0; restore ra,s0,s1; addi sp,sp,32; jalr x0,0(t1) *)
    step. step. step. step. step. step. step.
    fix_pc_hv HEV.
    lazymatch goal with
    | H : rw_cells _ ?mX (bv_unsigned sp + -32) _, S : stk _ ?mX lo _ |- _ => release_frame H S (bv_unsigned sp)
    end.
    unfold acgt_init_post_v, A_vdso_func. finish.
  Qed.

  (* -------- time() and clock_gettime() up to the vDSO call -------- *)

  Definition atime_front_post_v (sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v s4v : word)
      (F : bvmap 5 word) (fc : bv 32) (lo can : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m1 : mem)
                      (junk16 junk8 junkA junkB : list byte),
      ms' = MS (mkR (Z_to_bv 64 ATW_CG_RET) (Z_to_bv 64 (bv_unsigned sp + -2224)) gp tp x5 x6 x7
                    (Z_to_bv 64 (bv_unsigned sp + -2192)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp + -2192))
                    x12 x13 x14 x15 x16 x17 s2 s3 (Z_to_bv 64 APAT) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 hvdso) fc None m1 (seg_rom VS)
      /\ rw_cells VS m1 (bv_unsigned sp + -2192)
           [CB 16 junk16; C8 (Z_to_bv 64 can); C8 (Z_to_bv 64 0); C8 sp; C8 (Z_to_bv 64 ATW_ICPT_RET)]
      /\ rw_cells VS m1 (bv_unsigned sp + -2224)
           [CB 8 junk8; C8 (Z_to_bv 64 ACANARY_CELL); C8 (Z_to_bv 64 (bv_unsigned sp + -80)); C8 (Z_to_bv 64 ATW_TIME_RET)]
      /\ rw_cells VS m1 (bv_unsigned sp + -2144)
           [CB 2064 junkA; C8 (Z_to_bv 64 APAT); CB 8 junkB; C8 s6; C8 s5; C8 s4v; C8 s3; C8 s2; C8 s1v; C8 s0v; C8 rav]
      /\ rw_cells VS m1 A_vdso_func [C8 (Z_to_bv 64 hvdso)]
      /\ rw_cells VS m1 AGOT_SSP_CELL [C8 (Z_to_bv 64 ACANARY_CELL)] /\ rw_cells VS m1 ACANARY_CELL [C8 (Z_to_bv 64 can)]
      /\ munch [(bv_unsigned sp - ATIME_STACK, bv_unsigned sp); (A_vdso_func, A_vdso_func + 8)]%Z m m1
      /\ wmono VS m m1 /\ mem_inv VS m1
      /\ stk VS m1 lo (bv_unsigned sp + -2224).

  Lemma atime_front_v : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo av vb vf can : Z),
    ro_cells VS m AAUXV_CELL [C8 (Z_to_bv 64 av)] ->
    ro_cells VS m av [C8 (Z_to_bv 64 33); C8 (Z_to_bv 64 vb)] ->
    rvdso_rom VS vb -> 0 < vb -> vb + 1460 = hvdso -> bv_unsigned sp <= av -> vb + RVDSO_SPAN <= lo ->
    rw_cells VS m AINITED_CELL [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)] ->
    rw_cells VS m ATIMEP_CELL [C8 (Z_to_bv 64 AREAL_TIME)] ->
    rw_cells VS m AGOT_SSP_CELL [C8 (Z_to_bv 64 ACANARY_CELL)] ->
    rw_cells VS m ACANARY_CELL [C8 (Z_to_bv 64 can)] -> 0 <= can < 2^64 ->
    rw_cells VS m A_vdso_func [C8 (Z_to_bv 64 vf)] -> (vf = hvdso \/ vf = P_cgt_init) ->
    astrcmp_cells tail m -> astrcmp_shz tail m VW_NAME 20 -> astrcmp_shz tail m VW_VERNAME 10 ->
    astrcmp_shz tail m (vb + AVW_STRTAB) (AVW_STRSZ - 1) ->
    stk VS m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ATIME_STACK -> mem_inv VS m ->
    a0 = Z_to_bv 64 0 ->
    evt VS (atime_front_post_v sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 ra s0 s1 s4 F fc lo can m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_time) fc None m (seg_rom VS)).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m lo av vb vf can CELL AUXP ROMv VBP HVBv SPA VBLO INIT TIMEP GOT CAN CANR VF HVF
           CELLS SZN SZV SZT ST CEIL LO MI A0.
    subst a0. acb.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof ROMv as (VB0 & VBA & VBH & _). rewrite RVDSO_SPAN_val in VBH.
    pose proof (ats_even_entry vb hvdso VBA HVBv) as HEV.
    unfold ATIME_STACK in LO.
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (A_vdso_func, A_vdso_func + 8)]%Z m) as MU.
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp)]%Z m) as MUs.
    pose proof (wmono_refl (asegs ++ tail) m) as WM.
    unfold A_vdso_func, P_cgt_init, AGOT_SSP_CELL, ACANARY_CELL, P_time, AINITED_CELL, ATIMEP_CELL, AREAL_TIME, AAUXV_CELL in *.
    (* P_time: [j 0x3b7c], to the interceptor *)
    step.
    (* the interceptor's prologue: addi sp,-0x7f0; eight saves; addi s0,sp,0x7f0; addi sp,-0x70; mv s1,a0 *)
    step. carve_frame 2144%nat ST. do 8 step. step. step. step.
    (* the init-once test, a sibling call with a 16-byte frame: asan_inited reads 1 *)
    (* the call and the callee's addi sp,sp,-16; the frame carved right after the addi, as the
       leaf walks do (As/AW_Leaves.v) *)
    zstep. zstep. carve_frame 16%nat ST.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -2160) _ |- _ => rename H into FRI end.
    (* sd ra ; sd s0 into the carved frame, as As/AsStrcmp.v's [st1] (Lib/TacX.v) stores over the run's
       list; then auipc ; addi ; lb ; li ; fence *)
    do 2 (step; fix_lit_store; try nrm).
    do 5 zstep.
    zstep. if_cases K; [exfalso; revert K; vm_compute; discriminate|]. clear K.
    do 4 zstep.
    fix_ret_lit.
    release_frame FRI ST (bv_unsigned sp + -2144).
    (* beqz a0 on its answer 1 *)
    zstep. if_cases K0; [exfalso; revert K0; vm_compute; discriminate|]. clear K0.
    (* auipc; ld s4: the pattern word in read-only data *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (RO : ro_cells (asegs ++ tail) mX ATW_PAT_CELL [C8 (Z_to_bv 64 APAT)]);
      [ lazymatch goal with MIx : mem_inv _ mX |- _ =>
          pose proof (ro_cells_image (asegs ++ tail) mX ATW_PAT_CELL (le8 (Z_to_bv 64 APAT)) MIx
                        ltac:(vm_compute; reflexivity) ltac:(unfold ATW_PAT_CELL; lia)
                        ltac:(unfold ATW_PAT_CELL; cbn; lia)) as RO0 end;
        destruct RO0 as [_ RB]; split; [cbn; repeat split; exact I | exact RB] |] end.
    unfold ATW_PAT_CELL in RO.
    step. step.
    (* auipc; ld a1 (REAL(time)); sd s4,-0x50(s0); addi a0,s0,-0x50; jalr a1 *)
    step. step. step. step. step.
    (* musl's time: frame, canary, a1 = sp, a0 = CLOCK_REALTIME, jal clock_gettime *)
    step. carve_frame 48%nat ST. do 10 lstep.
    (* clock_gettime: frame, s0 = ts, a2 = vdso_func, s1 = clk *)
    step. lstep. carve_frame 32%nat ST. do 7 lstep.
    destruct HVF as [-> | ->].
    - (* the entry is resolved: a2 != 0, then jalr ra,0(a2) *)
      step. if_false_nz. step. step. step. fix_pc_hv HEV.
      apply evt_done.
      unfold atime_front_post_v, A_vdso_func, AGOT_SSP_CELL, ACANARY_CELL, ATIME_STACK, ATW_CG_RET, ATW_ICPT_RET, ATW_TIME_RET.
      do 18 eexists. split; [reflexivity|].
      do 9 (split; [eassumption|]). eassumption.
    - (* the first call: a2 = cgt_init *)
      step. if_false. step. step. step.
      eapply evt_cut.
      { eapply acgt_init_v with (lo := lo) (av := av) (vb := vb).
        all: rewrite ?unsigned_lit by lia.
        all: first
          [ lazymatch goal with |- _ + RVDSO_SPAN <= _ => exact VBLO end
          | eassumption
          | (eapply av_cells_frame; [exact CELLS | exact MUs | unfold AIMG_TOP; lia])
          | (eapply av_shz_frame; [exact SZN | exact MUs | unfold AHI_LO; lia])
          | (eapply av_shz_frame; [exact SZV | exact MUs | unfold AHI_LO; lia])
          | (eapply av_shz_frame; [exact SZT | exact MUs | unfold AHI_LO; lia])
          | lia ]. }
      intros ms1 PG. unfold acgt_init_post_v in PG.
      destruct PG as (u0 & u1 & u2 & q2 & q3 & q4 & q5 & q6 & q7 & u3 & u4 & u5 & u6 & m2
                      & -> & MU1 & WM1 & MI1 & ST1 & VF1).
      rewrite unsigned_lit in MU1, ST1 by lia.
      unfold A_vdso_func in MU1, VF1.
      clear MUs. try clear VF. try clear CELL. try clear AUXP. try clear INIT. try clear TIMEP.
      lazymatch type of MU1 with munch _ ?m1 _ => aw_transport m1 m2 MU1 WM1 end.
      clear MU1 WM1. clear ST MI. rename ST1 into ST. rename MI1 into MI.
      apply evt_done.
      unfold atime_front_post_v, A_vdso_func, AGOT_SSP_CELL, ACANARY_CELL, ATIME_STACK, ATW_CG_RET, ATW_ICPT_RET, ATW_TIME_RET.
      do 18 eexists. split; [reflexivity|].
      do 9 (split; [eassumption|]). eassumption.
  Qed.

  (* -------- after the call: clock_gettime returns 0, time() and the interceptor return -------- *)

  Definition atime_back_post_v (sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v s4v : word)
      (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 (tv : word) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m' : mem),
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v tv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom VS)
      /\ munch [(bv_unsigned sp - ATIME_STACK, bv_unsigned sp)]%Z m m'
      /\ wmono VS m m' /\ mem_inv VS m' /\ stk VS m' lo (bv_unsigned sp).

  (* The state the vDSO call leaves: pc = clock_gettime's return address, a0 = 0, the
     caller-saved registers drawn, the timespec's 16 bytes at sp - 2192 ([bs]); the frames are
     the front's. *)
  Lemma atime_back_v : forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word)
      (sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v s4v : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (lo can : Z) (bs jk0 junk8 junkA junkB : list byte),
    rw_cells VS m (bv_unsigned sp + -2192) [CB 16 bs; CB 0 jk0] ->
    rw_cells VS m (bv_unsigned sp + -2176) [C8 (Z_to_bv 64 can); C8 (Z_to_bv 64 0); C8 sp; C8 (Z_to_bv 64 ATW_ICPT_RET)] ->
    rw_cells VS m (bv_unsigned sp + -2224)
      [CB 8 junk8; C8 (Z_to_bv 64 ACANARY_CELL); C8 (Z_to_bv 64 (bv_unsigned sp + -80)); C8 (Z_to_bv 64 ATW_TIME_RET)] ->
    rw_cells VS m (bv_unsigned sp + -2144)
      [CB 2064 junkA; C8 (Z_to_bv 64 APAT); CB 8 junkB; C8 s6; C8 s5; C8 s4v; C8 s3; C8 s2; C8 s1v; C8 s0v; C8 rav] ->
    rw_cells VS m ACANARY_CELL [C8 (Z_to_bv 64 can)] -> 0 <= can < 2^64 ->
    stk VS m lo (bv_unsigned sp + -2224) -> aceil <= lo -> lo <= bv_unsigned sp - ATIME_STACK -> mem_inv VS m ->
    evt VS (atime_back_post_v sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v s4v F fc lo m)
        (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2224)) gp tp y5 y6 y7
                 (Z_to_bv 64 (bv_unsigned sp + -2192)) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 y11 y12 y13 y14 y15 y16 y17 s2 s3 (Z_to_bv 64 APAT) s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
            F (Z_to_bv 64 ATW_CG_RET) fc None m (seg_rom VS)).
  Proof.
    intros y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11
           rav s0v s1v s4v F fc m lo can bs jk0 junk8 junkA junkB F16 FRr FRb FRc CAN CANR ST CLO LO MI.
    acb.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    unfold ATIME_STACK in LO.
    unfold ACANARY_CELL, ATW_ICPT_RET, ATW_TIME_RET, ATW_CG_RET in *.
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl (asegs ++ tail) m) as WM.
    (* clock_gettime: r == 0; sext.w; restore ra,s0,s1; addi sp,sp,32; ret *)
    step. if_true. do 6 step.
    (* time: a0 = ts.tv_sec; t (the interceptor's local) is not NULL *)
    step. step. if_cases K2; zify_cond K2.
    { exfalso. revert K2. rewrite ?unsigned_lit_wrap. clear - SPR CLO LO ACEILB. intros K2. lia. }
    (* *t = a0; the canary check; restore ra,s0,s1; addi sp,sp,48; ret *)
    step. step. step. step. if_cases KC; zify_cond KC. { exfalso. apply KC. reflexivity. }
    step. step. step. step. step.
    (* the interceptor: t == NULL, straight to its epilogue *)
    step. if_true. step. do 8 step. step. step.
    release_frame FRb ST (bv_unsigned sp + -2192).
    release_frame F16 ST (bv_unsigned sp + -2176).
    release_frame FRr ST (bv_unsigned sp + -2144).
    release_frame FRc ST (bv_unsigned sp).
    apply evt_done. unfold atime_back_post_v, ATIME_STACK. do 16 eexists. split; [reflexivity|].
    do 3 (split; [eassumption|]). eassumption.
  Qed.

End HCW.
